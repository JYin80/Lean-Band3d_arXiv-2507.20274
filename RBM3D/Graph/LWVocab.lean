/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.ScalingOrder
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The graph vocabulary of the light-weight layer

The vocabulary of Section 7.1 (Definitions 7.3-7.10) on the record representation `LGraph E I`:
`E` the external vertices (labels fixed), `I` the internal vertices (labels summed), edges of three
kinds and a coefficient.

## Contents

* Sections 1-3: the record: `LData`, `SEdge`, `WEdge`, `DEdge`, `LGraph`, `LGraph.val`, molecules,
  counters; the nested graphs `NGraph`, `IsNested`, `NoGhost`, `GhostOK`.

## The definitions of the paper and the field or function that represents each

* `def_graph1`: no new field is needed.  Predicates and relabelling of the vertices (section 4).
  The condition "at most one dotted edge per pair" is not enforced by the record.
* `ValG`: `LGraph.val`; a linear combination is a list of `PGraph E` (a graph with its own vertex
  types and the map `ext` of the original external vertices), `LComb.val`.
* molecules `def_poly`: `mol` is the connected component of the waved and `=`-dotted edges
  (`mem_mol_iff`), `Mol`, `molOf`, `IsExtMol`, `molSolid` (the molecular graph), `nM_eq_card`
  (`n_M` counts the internal molecules).
* normal graphs `defnlvl0`: the predicate `LGraph.Normal`.
* the dotted edge partition `dot-def`: `dotChoices` (expansion of the dotted edges), `withDots`,
  `merge` (vertices joined by `=`-dotted edges), `splitWeights` (weights to light-weights and a
  coefficient `m`), `partition : List (PGraph E)`; `val_eq_partition` (the value is the value of
  the combination), `partition_normal` (every term is a normal graph).
* scaling size `def scaling` and scaling order `def scaling order`: `Counters.scalingSize`,
  `LGraph.scalingSize`, `scalingOrder` for normal graphs (`RBM.Graph.ord`), `scalingSize_eq`.
* counters are invariant under a relabelling by a bijection (`counters_relabel_equiv`).

Reused from `RBM3D/Graph/ScalingOrder.lean`: `RBM.Graph.Counters`, `RBM.Graph.ord`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

/-! ## 1. The vocabulary: a multigraph record with typed vertex sets -/

namespace RBM.Graph

/-- The matrices a graph reads, on the index type `ι` of vertex labels (`ι = Idx d L W`):
`G` the resolvent `G = (H - z)⁻¹`, `M` its deterministic centre (`M = m I` for the random band
matrix, `Mres` in general), `S` the variance matrix, `Sp` the matrix `S⁺` of `(eq:def-Spm)`.
`Ḡ_{xy} = conj G_{xy}`, `S⁻_{xy} = conj S⁺_{yx}` (`S⁻ = (S⁺)^*`). -/
structure LData (ι : Type*) where
  G : Matrix ι ι ℂ
  M : Matrix ι ι ℂ
  S : Matrix ι ι ℂ
  Sp : Matrix ι ι ℂ

/-- A solid edge (`def_graph1`): blue (`σ = true`, charge `+`, `G_{xy}`) or red
(`σ = false`, `Ḡ_{xy}`), with (`circ`) or without a circle (`(G-M)_{xy}`); `src = dst` is a weight
(a self-loop). -/
structure SEdge (V : Type*) where
  σ : Bool
  circ : Bool
  src : V
  dst : V

/-- A waved edge (`def_graph1`): black `S_{xy}` (`col = false`) or coloured `S^±_{xy}`. -/
structure WEdge (V : Type*) where
  col : Bool
  σ : Bool
  x : V
  y : V

/-- A dotted edge (`def_graph1`): `1_{x=y}` (`eq = true`) or the `×`-dotted `1_{x≠y}`. -/
structure DEdge (V : Type*) where
  eq : Bool
  x : V
  y : V

/-- A **vertex-level graph** (`def_graph1`): `E` external vertices (labels fixed), `I` internal
vertices (labels summed), edges of the three kinds, and a coefficient.  The vertex set of the
edges is `E ⊕ I`. -/
structure LGraph (E I : Type*) where
  solid : List (SEdge (E ⊕ I))
  waved : List (WEdge (E ⊕ I))
  dotted : List (DEdge (E ⊕ I))
  coeff : ℂ

section Value

variable {ι V E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- The factor of a solid edge at the labelling `ℓ`. -/
def SEdge.val (D : LData ι) (ℓ : V → ι) (e : SEdge V) : ℂ :=
  let g : ℂ := D.G (ℓ e.src) (ℓ e.dst) - if e.circ then D.M (ℓ e.src) (ℓ e.dst) else 0
  if e.σ then g else star g

/-- The factor of a waved edge. -/
def WEdge.val (D : LData ι) (ℓ : V → ι) (e : WEdge V) : ℂ :=
  if e.col then (if e.σ then D.Sp (ℓ e.x) (ℓ e.y) else star (D.Sp (ℓ e.y) (ℓ e.x)))
  else D.S (ℓ e.x) (ℓ e.y)

/-- The factor of a dotted edge. -/
def DEdge.val (ℓ : V → ι) (e : DEdge V) : ℂ :=
  if (ℓ e.x = ℓ e.y) ↔ (e.eq = true) then 1 else 0

/-- The product of all edge factors and the coefficient at a labelling of all vertices. -/
def LGraph.term (Γ : LGraph E I) (D : LData ι) (ℓ : E ⊕ I → ι) : ℂ :=
  Γ.coeff * (Γ.solid.map (SEdge.val D ℓ)).prod * (Γ.waved.map (WEdge.val D ℓ)).prod *
    (Γ.dotted.map (DEdge.val ℓ)).prod

/-- **`ValG`**: the product of the edge factors and the coefficient, summed over the
labels of the internal vertices; the external labels are `ℓe`. -/
def LGraph.val (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)

omit [DecidableEq ι] in
/-- The sum over labellings of `n+1` vertices is an iterated sum. -/
theorem sum_pi_fin_succ {n : ℕ} (F : (Fin (n + 1) → ι) → ℂ) :
    ∑ ℓ : Fin (n + 1) → ι, F ℓ = ∑ a : ι, ∑ ℓ' : Fin n → ι, F (Matrix.vecCons a ℓ') := by
  rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] in
theorem sum_pi_fin_zero (F : (Fin 0 → ι) → ℂ) : ∑ ℓ : Fin 0 → ι, F ℓ = F ![] := by
  rw [Fintype.sum_unique]
  congr 1

end Value

section Counters

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `x` and `y` are joined by a waved edge or a dotted `=` edge (`def_poly`). -/
def LGraph.adj (Γ : LGraph E I) (u v : E ⊕ I) : Bool :=
  Γ.waved.any (fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) ||
  Γ.dotted.any (fun e => e.eq && decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)))

/-- One step of the neighbourhood closure. -/
def LGraph.step (Γ : LGraph E I) (s : Finset (E ⊕ I)) : Finset (E ⊕ I) :=
  s ∪ Finset.univ.filter (fun w => ∃ v ∈ s, Γ.adj v w = true)

/-- The molecule of `v` (`def_poly`): the closure of `{v}` under dotted and waved edges
(`|E ⊕ I|` steps reach the fixed point). -/
def LGraph.mol (Γ : LGraph E I) (v : E ⊕ I) : Finset (E ⊕ I) :=
  (Γ.step)^[Fintype.card (E ⊕ I)] {v}

/-- `n_S`: the number of solid edges (weights included). -/
def LGraph.nS (Γ : LGraph E I) : ℕ := Γ.solid.length
/-- `n_W`: the number of waved edges. -/
def LGraph.nW (Γ : LGraph E I) : ℕ := Γ.waved.length
/-- `n_V`: the number of internal vertices. -/
def LGraph.nV (_ : LGraph E I) : ℕ := Fintype.card I
/-- `n_M`: the number of internal molecules (molecules without an external vertex). -/
def LGraph.nM (Γ : LGraph E I) : ℕ :=
  ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.mol v, w.isRight = true)).image Γ.mol).card

/-- The counters of `def scaling` / `def scaling order` in `RBM.Graph.Counters`
(`nlw`, `ndv` are bookkeeping counters of the case analysis of the scaling order, not invariants of the graph). -/
def LGraph.counters (Γ : LGraph E I) : Counters := ⟨Γ.nS, Γ.nW, Γ.nV, Γ.nM, 0, 0⟩

end Counters

section Examples

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `f_{xy}(G) = Σ_{α∉{x,y}} Σ_β S_{αβ} Ǧ_{ββ} G_{xα} G_{αy}` (`(fxyG_sum)`). -/
def fxyVal (D : LData ι) (x y : ι) : ℂ :=
  ∑ α, if α = x ∨ α = y then 0 else ∑ β, D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y

end Examples

/-! ## 3. Nested graphs (`lem:Anp_key`, `lem:Anp_key_gh`: Lemmas 7.23, 7.24)

The auxiliary graph of `def_auxgraph` has the block-level vertices `[a_i], [b_i]` (external) and
`[α_j]` (internal); its edges are solid (a factor `ξ`) or ghost (the factor `1`).  The
`p` edge-disjoint paths `𝔓_i` are part of the data: a path is its list of steps
`(edge, next vertex)` from `a_i`. -/

/-- The vertices of a nested graph: `a_i = inl (inl i)`, `b_i = inl (inr i)`, internal `inr j`. -/
abbrev NV (p q : ℕ) := (Fin p ⊕ Fin p) ⊕ Fin q

/-- An edge of a nested graph: solid or ghost. -/
structure NEdge (p q : ℕ) where
  ghost : Bool
  u : NV p q
  v : NV p q

/-- A nested graph with `p` paths and `q` internal vertices: the edges and the paths. -/
structure NGraph (p q : ℕ) where
  es : List (NEdge p q)
  path : Fin p → List (Fin es.length × NV p q)

namespace NGraph

variable {p q : ℕ} (Γ : NGraph p q)

/-- The path `i` is a walk `a_i → b_i`: each step takes an edge from the current vertex. -/
def WalkOK (i : Fin p) : Prop :=
  ((Γ.path i).foldl (fun (acc : Option (NV p q)) st => acc.bind fun c =>
      if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
          ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none)
    (some (Sum.inl (Sum.inl i)))) = some (Sum.inl (Sum.inr i))

/-- `𝔓_i` passes through the vertex `v`. -/
def Visits (i : Fin p) (v : NV p q) : Prop :=
  ∃ st ∈ Γ.path i, (Γ.es.get st.1).u = v ∨ (Γ.es.get st.1).v = v

instance (i : Fin p) (v : NV p q) : Decidable (Γ.Visits i v) := by unfold Visits; infer_instance

/-- The path properties (1)-(3) of `lem:Anp_key` (Lemma 7.23), no self-loops: (1) `p`
edge-disjoint paths `𝔓_i : a_i → b_i`; (2) each internal vertex lies on two distinct paths (so it has
degree `≥ 4`); (3) every set `A` of internal vertices lies on at least `|A|` paths. -/
def IsNested : Prop :=
  (∀ e ∈ Γ.es, e.u ≠ e.v) ∧
  (∀ i, Γ.WalkOK i) ∧
  (∀ i, ((Γ.path i).map Prod.fst).Nodup) ∧
  (∀ i j, i ≠ j → ∀ st ∈ Γ.path i, ∀ st' ∈ Γ.path j, st.1 ≠ st'.1) ∧
  (∀ α : Fin q, ∃ i j, i ≠ j ∧ Γ.Visits i (Sum.inr α) ∧ Γ.Visits j (Sum.inr α)) ∧
  (∀ A : Finset (Fin q), A.card ≤ (Finset.univ.filter fun j : Fin p => ∃ α ∈ A, Γ.Visits j (Sum.inr α)).card)

/-- No ghost edge (`lem:Anp_key`). -/
def NoGhost : Prop := ∀ e ∈ Γ.es, e.ghost = false

/-- The ghost condition of `lem:Anp_key_gh` (Lemma 7.24): each path has at most one ghost edge, and it
is an ending edge (the first or the last step). -/
def GhostOK : Prop :=
  ∀ i, (((Γ.path i).filter fun st => (Γ.es.get st.1).ghost).length ≤ 1) ∧
    ∀ st ∈ Γ.path i, (Γ.es.get st.1).ghost = true → (Γ.path i).head? = some st ∨ (Γ.path i).getLast? = some st

/-- The number of solid (non-ghost) edges. -/
def nSolid : ℕ := (Γ.es.filter fun e => !e.ghost).length

/-- The path `i` has no ghost edge. -/
def noGhostPath (i : Fin p) : Bool := (Γ.path i).all fun st => !(Γ.es.get st.1).ghost

/-- `n_ngh`: the number of paths without a ghost edge (Lemma 7.24). -/
def nngh : ℕ := (Finset.univ.filter fun i : Fin p => Γ.noGhostPath i = true).card

/-- `ord(𝒢) = #solid edges - 2 #internal vertices` (`(eq:ordGaux)`): the
`RBM.Graph.ord` with `n_W = 0` and `n_V = q`. -/
def ordN : ℤ := ord ⟨Γ.nSolid, 0, q, 0, 0, 0⟩

/-- The value (`ValG` for the auxiliary graph): the edge `{u, v}` carries `ξ` of its labels, a ghost
edge `1`; internal labels are summed, `a`, `b` are the external labels. -/
def val {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (a b : Fin p → ι) : ℝ :=
  ∑ ℓ : Fin q → ι, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod

end NGraph

/-! ## 4. Predicates and relabelling: `def_graph1`

The record of section 1 already carries every edge kind of `def_graph1`: solid edges
`G`, `Ḡ`, `G - M`, `\overline{G - M}` (`SEdge`, the flags `σ` and `circ`), weights and light-weights
(`SEdge` with `src = dst`), waved edges `S`, `S^±` (`WEdge`), dotted and `×`-dotted edges (`DEdge`),
the coefficient (`coeff`).  No field is added for `def_graph1`
itself; only the relabelling of the vertices of a graph and the packing of graphs with their own
internal vertex types, which a linear combination needs. -/

section Edges

variable {V W : Type*}

/-- Relabelling of the end vertices of a solid edge. -/
def SEdge.map (f : V → W) (e : SEdge V) : SEdge W := ⟨e.σ, e.circ, f e.src, f e.dst⟩

/-- Relabelling of the end vertices of a waved edge. -/
def WEdge.map (f : V → W) (e : WEdge V) : WEdge W := ⟨e.col, e.σ, f e.x, f e.y⟩

/-- Relabelling of the end vertices of a dotted edge. -/
def DEdge.map (f : V → W) (e : DEdge V) : DEdge W := ⟨e.eq, f e.x, f e.y⟩

end Edges

section Relabel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E E' I I' V W : Type*}

/-- Relabelling of the vertices of a graph by a map `φ` of the vertex sets (merging vertices when `φ`
is not injective, renaming them when it is a bijection). -/
def LGraph.relabel (Γ : LGraph E I) (φ : E ⊕ I → E' ⊕ I') : LGraph E' I' where
  solid := Γ.solid.map (SEdge.map φ)
  waved := Γ.waved.map (WEdge.map φ)
  dotted := Γ.dotted.map (DEdge.map φ)
  coeff := Γ.coeff

/-- The product of the edge factors of a relabelled graph is that of the graph at the pulled-back
labelling. -/
theorem LGraph.term_relabel (Γ : LGraph E I) (φ : E ⊕ I → E' ⊕ I') (D : LData ι)
    (ℓ : E' ⊕ I' → ι) : (Γ.relabel φ).term D ℓ = Γ.term D (ℓ ∘ φ) := by
  simp only [LGraph.term, LGraph.relabel, List.map_map]
  rfl

end Relabel

/-! ## 5. Molecules (`def_poly`)

"Two vertices belong to the same molecule if and only if they are connected by a path of dotted and
waved edges."  `LGraph.mol` computes the closure by `|E ⊕ I|` neighbourhood steps;
`mem_mol_iff` shows that it is the connected component in the graph `molGraph` of the waved edges
and the `=`-dotted edges (the `×`-dotted edges do not connect).  The record needs no new field: the
molecules are computed from `waved` and `dotted`. -/

section Mol

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem LGraph.adj_comm (Γ : LGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [LGraph.adj, or_comm]

/-- The graph on the vertices whose edges are the waved edges and the `=`-dotted edges (`def_poly`). -/
def LGraph.molGraph (Γ : LGraph E I) : SimpleGraph (E ⊕ I) :=
  SimpleGraph.fromRel fun u v => Γ.adj u v = true

private theorem LGraph.molGraph_adj (Γ : LGraph E I) (u v : E ⊕ I) :
    Γ.molGraph.Adj u v ↔ u ≠ v ∧ Γ.adj u v = true := by
  simp only [LGraph.molGraph, SimpleGraph.fromRel_adj, Γ.adj_comm v u, or_self]

private theorem LGraph.subset_step (Γ : LGraph E I) (s : Finset (E ⊕ I)) : s ⊆ Γ.step s :=
  Finset.subset_union_left

private theorem LGraph.step_mono (Γ : LGraph E I) : Monotone Γ.step := by
  intro s t h w hw
  simp only [LGraph.step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with hw | ⟨v, hv, hadj⟩
  · exact Or.inl (h hw)
  · exact Or.inr ⟨v, h hv, hadj⟩

private theorem LGraph.subset_iterate (Γ : LGraph E I) (n : ℕ) (s : Finset (E ⊕ I)) :
    s ⊆ Γ.step^[n] s := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (Γ.subset_step _)

private theorem LGraph.iterate_mono_nat (Γ : LGraph E I) {n m : ℕ} (h : n ≤ m) (s : Finset (E ⊕ I)) :
    Γ.step^[n] s ⊆ Γ.step^[m] s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact Γ.subset_iterate k _

private theorem LGraph.reachable_of_mem_iterate (Γ : LGraph E I) (n : ℕ) :
    ∀ (v w : E ⊕ I), w ∈ Γ.step^[n] {v} → Γ.molGraph.Reachable v w := by
  induction n with
  | zero => intro v w h; simp only [Function.iterate_zero, id, Finset.mem_singleton] at h; subst h; exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro v w h
    rw [Function.iterate_succ_apply'] at h
    simp only [LGraph.step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | ⟨u, hu, hadj⟩
    · exact ih v w h
    · have h1 := ih v u hu
      by_cases huw : u = w
      · subst huw; exact h1
      · exact h1.trans (SimpleGraph.Adj.reachable ((Γ.molGraph_adj u w).2 ⟨huw, hadj⟩))

private theorem LGraph.walk_mem_iterate (Γ : LGraph E I) {v w : E ⊕ I} (p : Γ.molGraph.Walk v w) :
    w ∈ Γ.step^[p.length] {v} := by
  induction p with
  | nil => simp
  | @cons u v' w' h p ih =>
    rw [SimpleGraph.Walk.length_cons, Function.iterate_succ_apply]
    refine (Γ.step_mono.iterate p.length) ?_ ih
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp only [LGraph.step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact Or.inr ⟨u, rfl, ((Γ.molGraph_adj u x).1 h).2⟩

/-- `mol` is the molecule of `def_poly`: the connected component of `v` in the graph of
waved and `=`-dotted edges. -/
theorem LGraph.mem_mol_iff (Γ : LGraph E I) (v w : E ⊕ I) :
    w ∈ Γ.mol v ↔ Γ.molGraph.Reachable v w := by
  constructor
  · exact Γ.reachable_of_mem_iterate _ v w
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    exact Γ.iterate_mono_nat hp.length_lt.le _ (Γ.walk_mem_iterate p)

/-! The molecules as connected components, the external and internal molecules, edges inside a
molecule and the solid edges of the molecular graph `𝒢_ℳ` (`def_poly`). -/

/-- The set of molecules: the connected components of `molGraph` (`def_poly`). -/
abbrev LGraph.Mol (Γ : LGraph E I) : Type _ := Γ.molGraph.ConnectedComponent

/-- The molecule of a vertex (`def_poly`). -/
def LGraph.molOf (Γ : LGraph E I) (v : E ⊕ I) : Γ.Mol := Γ.molGraph.connectedComponentMk v

/-- Two vertices are in the same molecule iff one is in the closure `mol` of the other. -/
theorem LGraph.molOf_eq_iff (Γ : LGraph E I) (u v : E ⊕ I) :
    Γ.molOf u = Γ.molOf v ↔ v ∈ Γ.mol u := by
  rw [Γ.mem_mol_iff]; exact SimpleGraph.ConnectedComponent.eq

/-- External molecule: it contains an external vertex (`def_poly`). -/
def LGraph.IsExtMol (Γ : LGraph E I) (c : Γ.Mol) : Prop := ∃ a : E, Γ.molOf (Sum.inl a) = c

/-- An edge is *inside* a molecule if both of its ends belong to it (`def_poly`). -/
def LGraph.InsideMol (Γ : LGraph E I) (u v : E ⊕ I) : Prop := Γ.molOf u = Γ.molOf v

/-- The solid edges of the molecular graph `𝒢_ℳ` (`def_poly`): the vertices are the molecules,
the solid edges between different molecules are kept (their ends replaced by the molecules), and all
other components (`×`-dotted edges, edges inside molecules, the coefficient) are discarded.  The
waved and dotted edges are discarded as well: they lie inside molecules by definition. -/
def LGraph.molSolid (Γ : LGraph E I) : List (SEdge Γ.Mol) :=
  open Classical in
  (Γ.solid.filter fun e => ¬ Γ.InsideMol e.src e.dst).map (SEdge.map Γ.molOf)

/-- A molecule is internal iff all its vertices are internal. -/
theorem LGraph.forall_mol_isRight_iff (Γ : LGraph E I) (v : E ⊕ I) :
    (∀ w ∈ Γ.mol v, w.isRight = true) ↔ ¬ Γ.IsExtMol (Γ.molOf v) := by
  constructor
  · rintro h ⟨a, ha⟩
    have := h (Sum.inl a) ((Γ.molOf_eq_iff v (Sum.inl a)).1 ha.symm)
    simp at this
  · intro h w hw
    by_contra hr
    apply h
    rcases w with a | b
    · exact ⟨a, ((Γ.molOf_eq_iff v (Sum.inl a)).2 hw).symm⟩
    · simp at hr

/-- `n_M` is the number of internal molecules, the connected components with no external vertex
(`def_poly`, `def scaling`). -/
theorem LGraph.nM_eq_card (Γ : LGraph E I) :
    Γ.nM = Nat.card {c : Γ.Mol // ¬ Γ.IsExtMol c} := by
  classical
  have : Fintype Γ.Mol := Fintype.ofFinite _
  let Φ : Γ.Mol → Finset (E ⊕ I) := fun c => Finset.univ.filter fun w => Γ.molOf w = c
  have hmol : ∀ v, Γ.mol v = Φ (Γ.molOf v) := by
    intro v; ext w
    simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [eq_comm (a := Γ.molOf w), Γ.molOf_eq_iff]
  have hΦinj : Function.Injective Φ := by
    intro c c' h
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    have hv : v ∈ Φ (Γ.molGraph.connectedComponentMk v) := by simp [Φ, LGraph.molOf]
    rw [h] at hv
    simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hv
  have hnM : Γ.nM = (Finset.univ.filter fun c : Γ.Mol => ¬ Γ.IsExtMol c).card := by
    unfold LGraph.nM
    rw [← Finset.card_image_of_injective _ hΦinj]
    congr 1
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨Γ.molOf v, (Γ.forall_mol_isRight_iff v).1 hv, (hmol v).symm⟩
    · rintro ⟨c, hc, rfl⟩
      induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
      exact ⟨v, (Γ.forall_mol_isRight_iff v).2 hc, hmol v⟩
  rw [hnM, Nat.card_eq_fintype_card, Fintype.card_subtype]

end Mol
/-! ## 6. Packed graphs and linear combinations (`ValG`)

The graphs of a linear combination `∑ c_i 𝒢_i` have different internal vertex sets, and a graph
obtained by merging vertices (the dotted edge partition, sections 7-10) has fewer external vertices than
the original.  A `PGraph E` is a graph `g : LGraph E' I'` together with a surjection `ext : E → E'`:
the external vertices of the original graph are read through `ext`, so that two external vertices
that were merged must carry the same label (`PGraph.val` is `0` otherwise).  The coefficient `c_i` of
the term is the field `coeff` of `g`: the record keeps `coeff : ℂ`.  No field is added to `LGraph`;
the wrapper `PGraph` is new. -/

/-- A graph whose external vertices are the image of those of `E`, with its own vertex types: a term
of a linear combination (`ValG`) or a merged graph (`dot-def`). -/
structure PGraph (E : Type) where
  E' : Type
  I' : Type
  [instFE : Fintype E']
  [instDE : DecidableEq E']
  [instFI : Fintype I']
  [instDI : DecidableEq I']
  ext : E → E'
  ext_surj : Function.Surjective ext
  g : LGraph E' I'

attribute [instance] PGraph.instFE PGraph.instDE PGraph.instFI PGraph.instDI

section Packed

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type}

/-- The value of a packed graph at the external labels `ℓe : E → ι`: the value of `g` at the labels
`ℓ'` with `ℓe = ℓ' ∘ ext` if there is one (it is unique since `ext` is onto), and `0` if two merged
external vertices carry different labels (`ValG`). -/
def PGraph.val (P : PGraph E) (D : LData ι) (ℓe : E → ι) : ℂ :=
  open Classical in
  if h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext then P.g.val D h.choose else 0

/-- If the external labels factor through `ext`, the packed value is the value of the graph at the factored labels. -/
theorem PGraph.val_of_factor (P : PGraph E) (D : LData ι) {ℓe : E → ι} {ℓ' : P.E' → ι}
    (h : ℓe = ℓ' ∘ P.ext) : P.val D ℓe = P.g.val D ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [PGraph.val, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

/-- If the external labels do not factor through `ext` (two merged external vertices carry different labels), the packed value is `0`. -/
theorem PGraph.val_of_not (P : PGraph E) (D : LData ι) {ℓe : E → ι}
    (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : P.val D ℓe = 0 := by
  classical
  simp only [PGraph.val, h, ↓reduceDIte]

/-- A graph is a packed graph (no merging; `ValG`). -/
def LGraph.pack {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) : PGraph E where
  E' := E
  I' := I
  ext := id
  ext_surj := Function.surjective_id
  g := Γ

/-- A graph packed without merging has its own value. -/
theorem LGraph.pack_val {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) : Γ.pack.val D ℓe = Γ.val D ℓe :=
  PGraph.val_of_factor Γ.pack D (ℓ' := ℓe) rfl

/-- The value of a linear combination of graphs: the sum of the values of the terms (the
coefficients are inside the terms; `ValG`). -/
def LComb.val (L : List (PGraph E)) (D : LData ι) (ℓe : E → ι) : ℂ :=
  (L.map fun P => P.val D ℓe).sum

end Packed

/-! ## 7. Merging the vertices joined by `=`-dotted edges (`dot-def`)

"We merge vertices connected by dotted edges."  The classes of the equivalence relation generated by
the `=`-dotted edges are the vertices of the merged graph; a class is external if it contains an
external vertex (its label is then fixed), internal otherwise.  What the paper leaves implicit
: (1) an internal vertex merged with an external one becomes external;
(2) two external vertices in one class must carry the same label (`PGraph.val`); (3) each merged
graph has its own vertex types, hence the wrapper `PGraph`; the record `LGraph` needs no new field. -/

section Merge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `u`, `v` are the two ends of a `=`-dotted edge (`dot-def`). -/
def LGraph.EqRel (Γ : LGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ e ∈ Γ.dotted, e.eq = true ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))

/-- "Connected by a path of dotted edges" (`dot-def`): the equivalence relation generated by `EqRel`. -/
def LGraph.eqSetoid (Γ : LGraph E I) : Setoid (E ⊕ I) := Relation.EqvGen.setoid Γ.EqRel

/-- The vertices of the merged graph (`dot-def`). -/
abbrev LGraph.Cls (Γ : LGraph E I) : Type := Quotient Γ.eqSetoid

/-- The class of a vertex. -/
abbrev LGraph.cls (Γ : LGraph E I) (v : E ⊕ I) : Γ.Cls := Quotient.mk Γ.eqSetoid v

/-- A class is external if it contains an external vertex (`dot-def`). -/
def LGraph.IsExtCls (Γ : LGraph E I) (q : Γ.Cls) : Prop := ∃ a : E, Γ.cls (Sum.inl a) = q

/-- The external vertices of the merged graph. -/
abbrev LGraph.ExtCls (Γ : LGraph E I) : Type := {q : Γ.Cls // Γ.IsExtCls q}

/-- The internal vertices of the merged graph. -/
abbrev LGraph.IntCls (Γ : LGraph E I) : Type := {q : Γ.Cls // ¬ Γ.IsExtCls q}

noncomputable instance (Γ : LGraph E I) : Fintype Γ.Cls := by
  classical exact Quotient.fintype _

noncomputable instance (Γ : LGraph E I) : DecidableEq Γ.Cls := Classical.decEq _

noncomputable instance (Γ : LGraph E I) : Fintype Γ.ExtCls := by classical exact inferInstance

noncomputable instance (Γ : LGraph E I) : Fintype Γ.IntCls := by classical exact inferInstance

noncomputable instance (Γ : LGraph E I) : DecidableEq Γ.ExtCls := Classical.decEq _

noncomputable instance (Γ : LGraph E I) : DecidableEq Γ.IntCls := Classical.decEq _

/-- The merge map on the classes: external classes to `inl`, internal ones to `inr`. -/
def LGraph.vmapC (Γ : LGraph E I) (q : Γ.Cls) : Γ.ExtCls ⊕ Γ.IntCls :=
  open Classical in
  if h : Γ.IsExtCls q then Sum.inl ⟨q, h⟩ else Sum.inr ⟨q, h⟩

/-- The merge map `E ⊕ I → ExtCls ⊕ IntCls`. -/
def LGraph.vmap (Γ : LGraph E I) (v : E ⊕ I) : Γ.ExtCls ⊕ Γ.IntCls :=
  Γ.vmapC (Γ.cls v)

private theorem LGraph.vmap_eq_of_rel (Γ : LGraph E I) {u v : E ⊕ I} (h : Γ.EqRel u v) :
    Γ.vmap u = Γ.vmap v :=
  congrArg Γ.vmapC (Quotient.sound (Relation.EqvGen.rel _ _ h))

/-- The merged graph: the vertices of a class become one; the `=`-dotted edges disappear (they are
`1` after merging); a `×`-dotted edge inside a class makes the value `0` (`dot-def`, "inconsistent"). -/
def LGraph.merge (Γ : LGraph E I) : LGraph Γ.ExtCls Γ.IntCls where
  solid := Γ.solid.map (SEdge.map Γ.vmap)
  waved := Γ.waved.map (WEdge.map Γ.vmap)
  dotted := (Γ.dotted.filter fun e => !e.eq).map (DEdge.map Γ.vmap)
  coeff := Γ.coeff

/-- The external vertices of `Γ`, read in the merged graph. -/
def LGraph.extMap (Γ : LGraph E I) (a : E) : Γ.ExtCls := ⟨Γ.cls (Sum.inl a), a, rfl⟩

/-- Every external class has an external vertex (`ext` of a packed merge is onto). -/
theorem LGraph.extMap_surj (Γ : LGraph E I) : Function.Surjective Γ.extMap := by
  rintro ⟨q, a, rfl⟩
  exact ⟨a, rfl⟩

/-- The merged graph with its map of external vertices. -/
def LGraph.mergeP (Γ : LGraph E I) : PGraph E where
  E' := Γ.ExtCls
  I' := Γ.IntCls
  ext := Γ.extMap
  ext_surj := Γ.extMap_surj
  g := Γ.merge

end Merge

section MergeVal

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A labelling is constant on the `=`-dotted edges. -/
def LGraph.Good (Γ : LGraph E I) (ℓ : E ⊕ I → ι) : Prop := ∀ u v, Γ.EqRel u v → ℓ u = ℓ v

private theorem LGraph.Good.eq_of_cls {Γ : LGraph E I} {ℓ : E ⊕ I → ι} (h : Γ.Good ℓ) {u v : E ⊕ I}
    (huv : Γ.cls u = Γ.cls v) : ℓ u = ℓ v := by
  have h' : Relation.EqvGen Γ.EqRel u v := Quotient.exact huv
  clear huv
  induction h' with
  | rel _ _ hr => exact h _ _ hr
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A labelling that breaks a `=`-dotted edge makes the product of the edge factors vanish. -/
private theorem LGraph.term_eq_zero_of_not_good (Γ : LGraph E I) (D : LData ι) {ℓ : E ⊕ I → ι}
    (h : ¬ Γ.Good ℓ) : Γ.term D ℓ = 0 := by
  unfold LGraph.Good at h
  push Not at h
  obtain ⟨u, v, ⟨e, he, heq, hxy⟩, hne⟩ := h
  have hne' : ℓ e.x ≠ ℓ e.y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact fun h => hne h.symm
  have h0 : DEdge.val ℓ e = 0 := by simp [DEdge.val, heq, hne']
  have hprod : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)
  simp [LGraph.term, hprod]

private theorem LGraph.prod_dotted_merge (Γ : LGraph E I) (ℓ' : Γ.ExtCls ⊕ Γ.IntCls → ι) :
    ∀ l : List (DEdge (E ⊕ I)), (∀ e ∈ l, e ∈ Γ.dotted) →
      ((l.filter fun e => !e.eq).map (DEdge.val (ℓ' ∘ Γ.vmap))).prod =
        (l.map (DEdge.val (ℓ' ∘ Γ.vmap))).prod
  | [], _ => rfl
  | e :: l, h => by
    have ih := Γ.prod_dotted_merge ℓ' l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases heq : e.eq
    · simp [heq, ih]
    · have hv : Γ.vmap e.x = Γ.vmap e.y :=
        Γ.vmap_eq_of_rel ⟨e, h e (List.mem_cons_self), heq, Or.inl ⟨rfl, rfl⟩⟩
      have h1 : DEdge.val (ℓ' ∘ Γ.vmap) e = 1 := by simp [DEdge.val, heq, hv]
      simp [heq, ih, h1]

/-- The product of the edge factors of the merged graph is that of `Γ` at the pulled-back labelling. -/
private theorem LGraph.term_merge (Γ : LGraph E I) (D : LData ι) (ℓ' : Γ.ExtCls ⊕ Γ.IntCls → ι) :
    Γ.merge.term D ℓ' = Γ.term D (ℓ' ∘ Γ.vmap) := by
  have hS : (SEdge.val D ℓ') ∘ (SEdge.map Γ.vmap) = SEdge.val D (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hW : (WEdge.val D ℓ') ∘ (WEdge.map Γ.vmap) = WEdge.val D (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hDm : (DEdge.val ℓ') ∘ (DEdge.map Γ.vmap) = DEdge.val (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hD := Γ.prod_dotted_merge ℓ' Γ.dotted fun e he => he
  simp only [LGraph.term, LGraph.merge, List.map_map, hS, hW, hDm]
  rw [hD]

private theorem LGraph.vmap_inl (Γ : LGraph E I) (a : E) : Γ.vmap (Sum.inl a) = Sum.inl (Γ.extMap a) := by
  have h : Γ.IsExtCls (Γ.cls (Sum.inl a)) := ⟨a, rfl⟩
  simp [LGraph.vmap, LGraph.vmapC, LGraph.extMap, h]

private theorem LGraph.vmap_inr_ext (Γ : LGraph E I) (b : I) (h : Γ.IsExtCls (Γ.cls (Sum.inr b))) :
    Γ.vmap (Sum.inr b) = Sum.inl ⟨Γ.cls (Sum.inr b), h⟩ := by
  simp [LGraph.vmap, LGraph.vmapC, h]

private theorem LGraph.vmap_inr_int (Γ : LGraph E I) (b : I) (h : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b))) :
    Γ.vmap (Sum.inr b) = Sum.inr ⟨Γ.cls (Sum.inr b), h⟩ := by
  simp [LGraph.vmap, LGraph.vmapC, h]

/-- Every internal class has an internal vertex. -/
private theorem LGraph.exists_inr_of_int (Γ : LGraph E I) (q : Γ.IntCls) :
    ∃ b : I, Γ.cls (Sum.inr b) = q.1 := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep q.1
  rcases v with a | b
  · exact absurd ⟨a, hv⟩ q.2
  · exact ⟨b, hv⟩

/-- **Merging preserves the value** (`dot-def`), for the external labels that factor
through the merge: `Γ.val` at `ℓ' ∘ extMap` is the value of the merged graph at `ℓ'`. -/
theorem LGraph.val_eq_merge_val (Γ : LGraph E I) (D : LData ι) (ℓ' : Γ.ExtCls → ι) :
    Γ.val D (ℓ' ∘ Γ.extMap) = Γ.merge.val D ℓ' := by
  classical
  set Φ : (Γ.IntCls → ι) → (I → ι) := fun ℓi' b => (Sum.elim ℓ' ℓi') (Γ.vmap (Sum.inr b)) with hΦ
  have hlab : ∀ ℓi', Sum.elim (ℓ' ∘ Γ.extMap) (Φ ℓi') = (Sum.elim ℓ' ℓi') ∘ Γ.vmap := by
    intro ℓi'
    funext v
    rcases v with a | b
    · simp [Γ.vmap_inl]
    · rfl
  have hRHS : Γ.merge.val D ℓ' = ∑ ℓi', Γ.term D (Sum.elim (ℓ' ∘ Γ.extMap) (Φ ℓi')) := by
    unfold LGraph.val
    refine Finset.sum_congr rfl fun ℓi' _ => ?_
    rw [Γ.term_merge, hlab]
  have hinj : Function.Injective Φ := by
    intro f g hfg
    funext q
    obtain ⟨b, hb⟩ := Γ.exists_inr_of_int q
    have hq : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b)) := by rw [hb]; exact q.2
    have hv : Γ.vmap (Sum.inr b) = Sum.inr q := by
      rw [Γ.vmap_inr_int b hq]
      congr 1
      exact Subtype.ext hb
    have := congrFun hfg b
    simpa [hΦ, hv] using this
  have hrange : ∀ ℓi : I → ι, ℓi ∉ Set.range Φ →
      Γ.term D (Sum.elim (ℓ' ∘ Γ.extMap) ℓi) = 0 := by
    intro ℓi hℓi
    apply Γ.term_eq_zero_of_not_good
    intro hgood
    apply hℓi
    refine ⟨fun q => ℓi (Classical.choose (Γ.exists_inr_of_int q)), ?_⟩
    funext b
    by_cases hext : Γ.IsExtCls (Γ.cls (Sum.inr b))
    · obtain ⟨a, ha⟩ := hext
      have h1 := hgood.eq_of_cls (u := Sum.inl a) (v := Sum.inr b) ha
      simp only [hΦ, Γ.vmap_inr_ext b ⟨a, ha⟩, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] at h1 ⊢
      rw [← h1]
      congr 1
      exact Subtype.ext ha.symm
    · have hc := Classical.choose_spec (Γ.exists_inr_of_int ⟨Γ.cls (Sum.inr b), hext⟩)
      have h1 := hgood.eq_of_cls (u := Sum.inr (Classical.choose (Γ.exists_inr_of_int ⟨Γ.cls (Sum.inr b), hext⟩)))
        (v := Sum.inr b) hc
      simp only [hΦ, Γ.vmap_inr_int b hext, Sum.elim_inr]
      simpa using h1
  rw [hRHS]
  unfold LGraph.val
  rw [← Finset.sum_image (f := fun ℓi => Γ.term D (Sum.elim (ℓ' ∘ Γ.extMap) ℓi))
    (fun x _ y _ h => hinj h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro ℓi _ hni
  apply hrange
  rintro ⟨x, hx⟩
  exact hni (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩)

/-- **The merged graph has the value of the graph** (`dot-def`): for all external labels, including
those that give different labels to merged external vertices (both values are `0`). -/
theorem LGraph.mergeP_val (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) :
    Γ.mergeP.val D ℓe = Γ.val D ℓe := by
  classical
  by_cases h : ∃ ℓ' : Γ.ExtCls → ι, ℓe = ℓ' ∘ Γ.extMap
  · obtain ⟨ℓ', hℓ⟩ := h
    rw [PGraph.val_of_factor Γ.mergeP D hℓ]
    subst hℓ
    exact (Γ.val_eq_merge_val D ℓ').symm
  · rw [PGraph.val_of_not Γ.mergeP D h]
    unfold LGraph.val
    refine (Finset.sum_eq_zero fun ℓi _ => Γ.term_eq_zero_of_not_good D ?_).symm
    intro hgood
    apply h
    refine ⟨fun q => ℓe (Classical.choose q.2), ?_⟩
    funext a
    have hc := Classical.choose_spec (Γ.extMap a).2
    have := hgood.eq_of_cls (u := Sum.inl (Classical.choose (Γ.extMap a).2)) (v := Sum.inl a) hc
    simpa using this.symm

end MergeVal

/-! ## 8. Normal graphs (`defnlvl0`)

The predicate reads the lists `solid` and `dotted` of the record; no new field is needed. -/

section Normal

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Γ` has a solid edge between the vertices `u` and `v` (in either direction), not a loop
(`defnlvl0` (iii)). -/
def LGraph.SBetween (Γ : LGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ e ∈ Γ.solid, e.src ≠ e.dst ∧ ((e.src = u ∧ e.dst = v) ∨ (e.src = v ∧ e.dst = u))

/-- `Γ` has a `×`-dotted edge `1_{x≠y}` between the vertices `u` and `v` (in either order)
(`defnlvl0` (iii)). -/
def LGraph.XBetween (Γ : LGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ e ∈ Γ.dotted, e.eq = false ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))

instance (Γ : LGraph E I) (u v : E ⊕ I) : Decidable (Γ.SBetween u v) := by
  unfold LGraph.SBetween; infer_instance

instance (Γ : LGraph E I) (u v : E ⊕ I) : Decidable (Γ.XBetween u v) := by
  unfold LGraph.XBetween; infer_instance

/-- **Normal graph** (`defnlvl0`): (ii) there are no (`=`-)dotted edges; (iii) two
different vertices are joined by a `×`-dotted edge if and only if they are joined by a solid edge;
(iv) every weight is a light-weight, i.e. every solid self-loop has a circle.  Condition (i), "at
most `O(1)` many vertices and edges", is not a property of a fixed record: it is the bound `n` that a
consumer quantifies outside (every `LGraph E I` with finite lists has finitely many).  Reading of
(iii): `defnlvl0` says "solid edge" and `dot-def` says "`G`-edge";
here every non-loop solid edge (`G`, `Ḡ`, `G-M`, `\overline{G-M}`) counts. -/
def LGraph.Normal (Γ : LGraph E I) : Prop :=
  (∀ e ∈ Γ.dotted, e.eq = false) ∧
  (∀ u v : E ⊕ I, u ≠ v → (Γ.XBetween u v ↔ Γ.SBetween u v)) ∧
  (∀ e ∈ Γ.solid, e.src = e.dst → e.circ = true)

instance (Γ : LGraph E I) : Decidable Γ.Normal := by unfold LGraph.Normal; infer_instance

end Normal

/-! ## 9. The dotted edge partition (`dot-def`), first half: the expansion of the dotted edges

For each pair of vertices `{α, β}` joined by a solid edge but by no `×`-dotted edge, write
`1 = 1_{α=β} + 1_{α≠β}`; for each `×`-dotted edge `1_{α≠β}` with no solid edge between
`α` and `β`, write `1_{α≠β} = 1 - 1_{α=β}`.  Expanding the product of all these identities
gives `Γ = ∑ Dot · Γ` (`odot`), each `Dot` a product of dotted and `×`-dotted edges with a sign.  An
`atom` is the list of the terms (sign, new dotted edges) of one identity; `lwCombineAtoms` expands the
product.  The record needs no new field.  A pair `{α, β}` with several solid edges is expanded once
(`lwDedupPairs`); every `×`-dotted edge without a solid edge is expanded once (at most one dotted
edge per pair is the paper's standing convention in `def_graph1`). -/

section Choices

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Two ordered pairs are the same unordered pair. -/
def lwSamePair {V : Type*} [DecidableEq V] (p q : V × V) : Bool :=
  decide ((p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1))

/-- Keep one representative of each unordered pair of a list. -/
def lwDedupPairs {V : Type*} [DecidableEq V] : List (V × V) → List (V × V)
  | [] => []
  | p :: l => if (lwDedupPairs l).any (lwSamePair p) then lwDedupPairs l else p :: lwDedupPairs l

private theorem lwSamePair_iff {V : Type*} [DecidableEq V] (p q : V × V) :
    lwSamePair p q = true ↔ (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1) := by
  simp [lwSamePair]

private theorem lwSamePair_comm {V : Type*} [DecidableEq V] (p q : V × V) : lwSamePair p q = lwSamePair q p := by
  rw [Bool.eq_iff_iff, lwSamePair_iff, lwSamePair_iff]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [h1, h2]

private theorem lwMem_of_mem_dedupPairs {V : Type*} [DecidableEq V] {l : List (V × V)} {p : V × V}
    (h : p ∈ lwDedupPairs l) : p ∈ l := by
  induction l with
  | nil => simp [lwDedupPairs] at h
  | cons q l ih =>
    simp only [lwDedupPairs] at h
    split_ifs at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

private theorem lwExists_mem_dedupPairs {V : Type*} [DecidableEq V] {l : List (V × V)} {p : V × V}
    (h : p ∈ l) : ∃ q ∈ lwDedupPairs l, lwSamePair q p = true := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
    simp only [lwDedupPairs]
    rcases List.mem_cons.1 h with rfl | h
    · split_ifs with hc
      · obtain ⟨x, hx, hxp⟩ := List.any_eq_true.1 hc
        exact ⟨x, hx, by rw [lwSamePair_comm]; exact hxp⟩
      · exact ⟨_, List.mem_cons_self, (lwSamePair_iff _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨x, hx, hxp⟩ := ih h
      split_ifs
      · exact ⟨x, hx, hxp⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, hxp⟩

/-- The pairs `{α, β}` with a solid edge but no `×`-dotted edge between them (one representative each;
`dot-def`). -/
def LGraph.aPairs (Γ : LGraph E I) : List ((E ⊕ I) × (E ⊕ I)) :=
  lwDedupPairs ((Γ.solid.filter fun e => decide (e.src ≠ e.dst ∧ ¬ Γ.XBetween e.src e.dst)).map
    fun e => (e.src, e.dst))

/-- The `×`-dotted edges with no solid edge between their ends (`dot-def`). -/
def LGraph.isB (Γ : LGraph E I) (e : DEdge (E ⊕ I)) : Bool :=
  decide (e.eq = false ∧ ¬ Γ.SBetween e.x e.y)

/-- The `×`-dotted edges to be replaced by `1 - 1_{α=β}` (`dot-def`). -/
def LGraph.bEdges (Γ : LGraph E I) : List (DEdge (E ⊕ I)) := Γ.dotted.filter Γ.isB

/-- The dotted edges kept unchanged (`dot-def`). -/
def LGraph.dotBase (Γ : LGraph E I) : List (DEdge (E ⊕ I)) := Γ.dotted.filter fun e => !Γ.isB e

/-- The identities of `dot-def`, as lists of terms (sign, new dotted edges). -/
def LGraph.dotAtoms (Γ : LGraph E I) : List (List (ℤ × List (DEdge (E ⊕ I)))) :=
  Γ.aPairs.map (fun p => [(1, [⟨true, p.1, p.2⟩]), (1, [⟨false, p.1, p.2⟩])]) ++
  Γ.bEdges.map (fun e => [(1, []), (-1, [⟨true, e.x, e.y⟩])])

/-- The product of a list of identities, expanded (`odot`). -/
def lwCombineAtoms {X : Type*} : List (List (ℤ × List X)) → List (ℤ × List X)
  | [] => [(1, [])]
  | a :: rest => a.flatMap fun o => (lwCombineAtoms rest).map fun c => (o.1 * c.1, o.2 ++ c.2)

/-- The terms `Dot` of the dotted edge partition: sign and the new dotted edges (`odot`). -/
def LGraph.dotChoices (Γ : LGraph E I) : List (ℤ × List (DEdge (E ⊕ I))) :=
  lwCombineAtoms Γ.dotAtoms

/-- The graph `Dot · Γ` of one term: the `×`-dotted edges without a solid edge are removed, the new
dotted edges are added, the sign goes into the coefficient (`dot-def`). -/
def LGraph.withDots (Γ : LGraph E I) (c : ℤ × List (DEdge (E ⊕ I))) : LGraph E I where
  solid := Γ.solid
  waved := Γ.waved
  dotted := Γ.dotBase ++ c.2
  coeff := (c.1 : ℂ) * Γ.coeff

private theorem lw_sum_flatMap {α β : Type*} [AddCommMonoid β] (a : List α) (g : α → List β) :
    (a.flatMap g).sum = (a.map fun x => (g x).sum).sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem lw_prod_split {α : Type*} (l : List α) (f : α → ℂ) (p : α → Bool) :
    (l.map f).prod = ((l.filter p).map f).prod * ((l.filter fun x => !p x).map f).prod := by
  induction l with
  | nil => simp
  | cons x l ih => cases hp : p x <;> simp [hp, ih] <;> ring

private theorem lw_sum_comm {α β : Type*} [Fintype α] (l : List β) (f : β → α → ℂ) :
    ∑ x, (l.map fun c => f c x).sum = (l.map fun c => ∑ x, f c x).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp [Finset.sum_add_distrib, ih]

section ChoicesVal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value of one identity at a labelling. -/
def lwEvalAtom {V : Type*} (ℓ : V → ι) (a : List (ℤ × List (DEdge V))) : ℂ :=
  (a.map fun o => (o.1 : ℂ) * (o.2.map (DEdge.val ℓ)).prod).sum

private theorem lwSum_combineAtoms {V : Type*} (ℓ : V → ι) :
    ∀ atoms : List (List (ℤ × List (DEdge V))),
      ((lwCombineAtoms atoms).map fun c => (c.1 : ℂ) * (c.2.map (DEdge.val ℓ)).prod).sum =
        (atoms.map (lwEvalAtom ℓ)).prod
  | [] => by simp [lwCombineAtoms]
  | a :: rest => by
    have ih := lwSum_combineAtoms ℓ rest
    rw [List.map_cons, List.prod_cons, ← ih, lwEvalAtom, lwCombineAtoms, List.map_flatMap,
      lw_sum_flatMap, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun o _ => ?_)
    rw [List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    simp only [Function.comp_apply, List.map_append, List.prod_append, Int.cast_mul]
    ring

/-- `1 = 1_{α=β} + 1_{α≠β}`. -/
private theorem lwEvalAtom_A {V : Type*} (ℓ : V → ι) (u v : V) :
    lwEvalAtom ℓ [(1, [⟨true, u, v⟩]), (1, [⟨false, u, v⟩])] = 1 := by
  by_cases h : ℓ u = ℓ v <;> simp [lwEvalAtom, DEdge.val, h]

/-- `1_{α≠β} = 1 - 1_{α=β}`. -/
private theorem lwEvalAtom_B {V : Type*} (ℓ : V → ι) (e : DEdge V) (he : e.eq = false) :
    lwEvalAtom ℓ [(1, []), (-1, [⟨true, e.x, e.y⟩])] = DEdge.val ℓ e := by
  by_cases h : ℓ e.x = ℓ e.y <;> simp [lwEvalAtom, DEdge.val, h, he]

private theorem LGraph.prod_dotAtoms (Γ : LGraph E I) (ℓ : E ⊕ I → ι) :
    (Γ.dotAtoms.map (lwEvalAtom ℓ)).prod = (Γ.bEdges.map (DEdge.val ℓ)).prod := by
  simp only [LGraph.dotAtoms, List.map_append, List.prod_append, List.map_map]
  have hA : (Γ.aPairs.map ((lwEvalAtom ℓ) ∘ fun p => [(1, [⟨true, p.1, p.2⟩]), (1, [⟨false, p.1, p.2⟩])])).prod
      = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
    exact lwEvalAtom_A ℓ p.1 p.2
  have hB : (Γ.bEdges.map ((lwEvalAtom ℓ) ∘ fun e => [(1, []), (-1, [⟨true, e.x, e.y⟩])])) =
      Γ.bEdges.map (DEdge.val ℓ) := by
    refine List.map_congr_left fun e he => ?_
    have : e.eq = false := by
      have := (List.mem_filter.1 he).2
      simp only [LGraph.isB, decide_eq_true_eq] at this
      exact this.1
    exact lwEvalAtom_B ℓ e this
  rw [hA, hB, one_mul]

/-- **The expansion of the dotted edges** (`odot`) at the level of the product of the edge
factors: the product at a labelling is the sum over the terms `Dot` of the products of `Dot · Γ`. -/
theorem LGraph.term_eq_sum_dotChoices (Γ : LGraph E I) (D : LData ι) (ℓ : E ⊕ I → ι) :
    Γ.term D ℓ = (Γ.dotChoices.map fun c => (Γ.withDots c).term D ℓ).sum := by
  have h1 : ∀ c : ℤ × List (DEdge (E ⊕ I)), (Γ.withDots c).term D ℓ =
      (Γ.coeff * (Γ.solid.map (SEdge.val D ℓ)).prod * (Γ.waved.map (WEdge.val D ℓ)).prod *
        (Γ.dotBase.map (DEdge.val ℓ)).prod) * ((c.1 : ℂ) * (c.2.map (DEdge.val ℓ)).prod) := by
    intro c
    simp only [LGraph.term, LGraph.withDots, List.map_append, List.prod_append]
    ring
  simp only [h1]
  rw [List.sum_map_mul_left, LGraph.dotChoices, lwSum_combineAtoms, Γ.prod_dotAtoms]
  simp only [LGraph.term]
  rw [lw_prod_split Γ.dotted (DEdge.val ℓ) Γ.isB]
  simp only [LGraph.bEdges, LGraph.dotBase]
  ring

/-- The expansion of the dotted edges at the level of values. -/
theorem LGraph.val_eq_sum_dotChoices (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) :
    Γ.val D ℓe = (Γ.dotChoices.map fun c => (Γ.withDots c).val D ℓe).sum := by
  unfold LGraph.val
  simp only [Γ.term_eq_sum_dotChoices]
  exact lw_sum_comm Γ.dotChoices fun c ℓi => (Γ.withDots c).term D (Sum.elim ℓe ℓi)

end ChoicesVal

end Choices

/-! ## 10. The partition: the weight split, consistency, and the list of normal graphs

After merging, "every diagonal factor `G_{xx}` (resp. `Ḡ_{xx}`) is decomposed into a light-weight
`(G_{xx} - m)` plus a coefficient `m` (resp. `\overline{(G_{xx} - m)}` plus `\bar m`)" (`dot-def`).
Here `M = m I` (`(eq:defMzsc)` (2.8)): the split needs `M_{xx} = m`, a hypothesis `∀ x, D.M x x = m` of the value
identities (`M` is a general matrix in `LData`).  `m` is a parameter of the partition: the coefficients
"polynomial in `m, m̄, …`" (`def_graph1`) are plain complex numbers in the record. -/

section Weights

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Split every weight (a self-loop without circle) of a list of solid edges into a light-weight and
a coefficient; the result is the list of terms (coefficient, edges) (`dot-def`). -/
def lwSplitLoops (m : ℂ) : List (SEdge V) → List (ℂ × List (SEdge V))
  | [] => [(1, [])]
  | e :: es => (lwSplitLoops m es).flatMap fun r =>
      if e.src = e.dst ∧ e.circ = false then
        [(r.1, ⟨e.σ, true, e.src, e.dst⟩ :: r.2), ((if e.σ then m else star m) * r.1, r.2)]
      else [(r.1, e :: r.2)]

private theorem lwProd_splitLoops (D : LData ι) {m : ℂ} (hM : ∀ x, D.M x x = m) (ℓ : V → ι) :
    ∀ es : List (SEdge V), (es.map (SEdge.val D ℓ)).prod =
      ((lwSplitLoops m es).map fun r => r.1 * (r.2.map (SEdge.val D ℓ)).prod).sum
  | [] => by simp [lwSplitLoops]
  | e :: es => by
    have ih := lwProd_splitLoops D hM ℓ es
    rw [List.map_cons, List.prod_cons, ih, lwSplitLoops, List.map_flatMap, lw_sum_flatMap,
      ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    by_cases h : e.src = e.dst ∧ e.circ = false
    · have hv : SEdge.val D ℓ e =
          SEdge.val D ℓ ⟨e.σ, true, e.src, e.dst⟩ + (if e.σ then m else star m) := by
        obtain ⟨h1, h2⟩ := h
        cases hσ : e.σ <;> simp [SEdge.val, h1, h2, hM, hσ]
      simp only [h, and_self, ↓reduceIte, List.map_cons, List.sum_cons, List.prod_cons, List.map_nil,
        List.sum_nil, add_zero, hv]
      ring
    · simp only [h, ↓reduceIte, List.map_cons, List.sum_cons, List.prod_cons, List.map_nil,
        List.sum_nil, add_zero]
      ring

end Weights

section Partition

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight split of a graph: every weight becomes a light-weight, with the coefficient `m` or
`m̄` (`dot-def`). -/
def LGraph.splitWeights (m : ℂ) (Δ : LGraph E I) : List (LGraph E I) :=
  (lwSplitLoops m Δ.solid).map fun r => { Δ with solid := r.2, coeff := r.1 * Δ.coeff }

/-- **The weight split preserves the value** (`dot-def`): `G_{xx} = (G_{xx} - m) + m` and `Ḡ_{xx} = \overline{(G_{xx} - m)} + \bar m` for `M_{xx} = m`. -/
theorem LGraph.val_splitWeights (m : ℂ) (Δ : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m)
    (ℓe : E → ι) :
    Δ.val D ℓe = ((Δ.splitWeights m).map fun g => g.val D ℓe).sum := by
  have hterm : ∀ ℓ : E ⊕ I → ι,
      Δ.term D ℓ = ((Δ.splitWeights m).map fun g => g.term D ℓ).sum := by
    intro ℓ
    have h1 := lwProd_splitLoops D hM ℓ Δ.solid
    simp only [LGraph.term, LGraph.splitWeights, List.map_map, Function.comp_def]
    rw [h1, ← List.sum_map_mul_left, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    ring
  unfold LGraph.val
  simp only [hterm]
  exact lw_sum_comm (Δ.splitWeights m) fun g ℓi => g.term D (Sum.elim ℓe ℓi)

/-- A term `Dot · Γ` is *inconsistent* if a `×`-dotted edge joins two vertices connected by a path of
dotted edges (`dot-def`): then `Dot · Γ = 0`. -/
def LGraph.Consistent (Γ : LGraph E I) : Prop :=
  ∀ e ∈ Γ.dotted, e.eq = false → ¬ Γ.cls e.x = Γ.cls e.y

/-- An inconsistent term `Dot · Γ` (a `×`-dotted edge inside a class of `=`-dotted edges) has product `0` at every labelling. -/
theorem LGraph.term_eq_zero_of_not_consistent (Γ : LGraph E I) (D : LData ι) (h : ¬ Γ.Consistent)
    (ℓ : E ⊕ I → ι) : Γ.term D ℓ = 0 := by
  by_cases hg : Γ.Good ℓ
  · unfold LGraph.Consistent at h
    push Not at h
    obtain ⟨e, he, hfalse, hcls⟩ := h
    have h0 : DEdge.val ℓ e = 0 := by simp [DEdge.val, hfalse, hg.eq_of_cls hcls]
    have hprod : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)
    simp [LGraph.term, hprod]
  · exact Γ.term_eq_zero_of_not_good D hg

/-- An inconsistent term `Dot · Γ` has value `0`. -/
theorem LGraph.val_eq_zero_of_not_consistent (Γ : LGraph E I) (D : LData ι) (h : ¬ Γ.Consistent)
    (ℓe : E → ι) : Γ.val D ℓe = 0 := by
  unfold LGraph.val
  exact Finset.sum_eq_zero fun ℓi _ => Γ.term_eq_zero_of_not_consistent D h _

/-- The merged graph of a term, with its weights split: a list of packed graphs (`dot-def`). -/
def LGraph.mergeSplitP (m : ℂ) (Δ : LGraph E I) : List (PGraph E) :=
  (Δ.merge.splitWeights m).map fun g =>
    { E' := Δ.ExtCls, I' := Δ.IntCls, ext := Δ.extMap, ext_surj := Δ.extMap_surj, g := g }

/-- The terms `Dot · Γ` of the dotted edge partition that are consistent (`dot-def`). -/
def LGraph.partitionTerms (Γ : LGraph E I) : List (LGraph E I) :=
  open Classical in
  (Γ.dotChoices.map Γ.withDots).filter fun Δ => decide Δ.Consistent

/-- **The dotted edge partition** (`dot-def`): the linear combination of normal graphs
`∑ Dot · Γ`, the terms `Dot` expanded (`dotChoices`), the inconsistent ones dropped (they are `0`),
the vertices joined by dotted edges merged (`merge`) and every weight split into a light-weight and a
coefficient (`splitWeights`). -/
def LGraph.partition (m : ℂ) (Γ : LGraph E I) : List (PGraph E) :=
  Γ.partitionTerms.flatMap (LGraph.mergeSplitP m)

/-- The merged graph of a term with its weights split has the value of the term. -/
theorem LGraph.mergeSplitP_val (m : ℂ) (Δ : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m)
    (ℓe : E → ι) : ((Δ.mergeSplitP m).map fun P => P.val D ℓe).sum = Δ.val D ℓe := by
  classical
  rw [← Δ.mergeP_val D ℓe]
  by_cases h : ∃ ℓ' : Δ.ExtCls → ι, ℓe = ℓ' ∘ Δ.extMap
  · obtain ⟨ℓ', hℓ⟩ := h
    have hm : Δ.mergeP.val D ℓe = Δ.merge.val D ℓ' := PGraph.val_of_factor Δ.mergeP D hℓ
    rw [hm, Δ.merge.val_splitWeights m D hM ℓ']
    unfold LGraph.mergeSplitP
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
    exact PGraph.val_of_factor _ D hℓ
  · rw [PGraph.val_of_not Δ.mergeP D h]
    unfold LGraph.mergeSplitP
    rw [List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨g, _, rfl⟩ := List.mem_map.1 hx
    exact PGraph.val_of_not _ D h

private theorem lw_sum_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℂ)
    (h : ∀ x ∈ l, p x = false → f x = 0) : ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases hp : p x
    · simp [hp, ih', h x List.mem_cons_self hp]
    · simp [hp, ih']

/-- **The dotted edge partition preserves the value** (`dot-def`): the value of `Γ` is
the value of the linear combination of normal graphs, for every external labelling, provided `M = m I`
on the diagonal (`D.M x x = m`). -/
theorem LGraph.val_eq_partition (m : ℂ) (Γ : LGraph E I) (D : LData ι) (hM : ∀ x, D.M x x = m)
    (ℓe : E → ι) : Γ.val D ℓe = LComb.val (Γ.partition m) D ℓe := by
  classical
  unfold LComb.val LGraph.partition
  rw [List.map_flatMap, lw_sum_flatMap]
  have h1 : (Γ.partitionTerms.map fun Δ => ((Δ.mergeSplitP m).map fun P => P.val D ℓe).sum) =
      Γ.partitionTerms.map fun Δ => Δ.val D ℓe := by
    refine List.map_congr_left fun Δ _ => Δ.mergeSplitP_val m D hM ℓe
  rw [h1, LGraph.partitionTerms, lw_sum_filter, List.map_map, Γ.val_eq_sum_dotChoices D ℓe]
  · rfl
  · intro Δ hΔ hp
    refine Δ.val_eq_zero_of_not_consistent D ?_ ℓe
    simpa using hp

end Partition

/-! ## 11. The terms of the partition are normal graphs -/

section PartitionNormal

private theorem lwCombineAtoms_mem_edge {X : Type*} :
    ∀ (atoms : List (List (ℤ × List X))) (c : ℤ × List X), c ∈ lwCombineAtoms atoms →
      ∀ e ∈ c.2, ∃ a ∈ atoms, ∃ o ∈ a, e ∈ o.2
  | [], c, hc, e, he => by
    simp only [lwCombineAtoms, List.mem_singleton] at hc
    subst hc
    simp at he
  | a :: rest, c, hc, e, he => by
    simp only [lwCombineAtoms, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨o, ho, c', hc', rfl⟩ := hc
    simp only [List.mem_append] at he
    rcases he with he | he
    · exact ⟨a, List.mem_cons_self, o, ho, he⟩
    · obtain ⟨a', ha', o', ho', he'⟩ := lwCombineAtoms_mem_edge rest c' hc' e he
      exact ⟨a', List.mem_cons_of_mem _ ha', o', ho', he'⟩

private theorem lwCombineAtoms_mem_option {X : Type*} :
    ∀ (atoms : List (List (ℤ × List X))) (c : ℤ × List X), c ∈ lwCombineAtoms atoms →
      ∀ a ∈ atoms, ∃ o ∈ a, ∀ e ∈ o.2, e ∈ c.2
  | [], c, hc, a, ha => by simp at ha
  | a₀ :: rest, c, hc, a, ha => by
    simp only [lwCombineAtoms, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨o, ho, c', hc', rfl⟩ := hc
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨o, ho, fun e he => List.mem_append.2 (Or.inl he)⟩
    · obtain ⟨o', ho', h'⟩ := lwCombineAtoms_mem_option rest c' hc' a ha
      exact ⟨o', ho', fun e he => List.mem_append.2 (Or.inr (h' e he))⟩

private theorem lwSplitLoops_props {V : Type*} [DecidableEq V] (m : ℂ) :
    ∀ (es : List (SEdge V)) (r : ℂ × List (SEdge V)), r ∈ lwSplitLoops m es →
      (∀ e ∈ r.2, e.src = e.dst → e.circ = true) ∧
      (∀ e ∈ r.2, e.src ≠ e.dst → e ∈ es) ∧
      (∀ e ∈ es, e.src ≠ e.dst → e ∈ r.2)
  | [], r, hr => by
    simp only [lwSplitLoops, List.mem_singleton] at hr
    subst hr
    simp
  | e₀ :: es, r, hr => by
    simp only [lwSplitLoops, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    obtain ⟨h1, h2, h3⟩ := lwSplitLoops_props m es r' hr'
    by_cases h : e₀.src = e₀.dst ∧ e₀.circ = false
    · simp only [h, and_self, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨?_, ?_, ?_⟩
        · intro e he hloop
          rcases List.mem_cons.1 he with rfl | he
          · rfl
          · exact h1 e he hloop
        · intro e he hne
          rcases List.mem_cons.1 he with rfl | he
          · exact absurd rfl hne
          · exact List.mem_cons_of_mem _ (h2 e he hne)
        · intro e he hne
          rcases List.mem_cons.1 he with rfl | he
          · exact absurd h.1 hne
          · exact List.mem_cons_of_mem _ (h3 e he hne)
      · refine ⟨h1, ?_, ?_⟩
        · intro e he hne
          exact List.mem_cons_of_mem _ (h2 e he hne)
        · intro e he hne
          rcases List.mem_cons.1 he with rfl | he
          · exact absurd h.1 hne
          · exact h3 e he hne
    · simp only [h, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      refine ⟨?_, ?_, ?_⟩
      · intro e he hloop
        rcases List.mem_cons.1 he with rfl | he
        · by_contra hc
          exact h ⟨hloop, by simpa using hc⟩
        · exact h1 e he hloop
      · intro e he hne
        rcases List.mem_cons.1 he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h2 e he hne)
      · intro e he hne
        rcases List.mem_cons.1 he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h3 e he hne)

private theorem LGraph.normal_of_split {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I']
    [DecidableEq I'] (m : ℂ) (Δ : LGraph E' I') (h2 : ∀ e ∈ Δ.dotted, e.eq = false)
    (h3 : ∀ u v : E' ⊕ I', u ≠ v → (Δ.XBetween u v ↔ Δ.SBetween u v)) :
    ∀ g ∈ Δ.splitWeights m, g.Normal := by
  intro g hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
  obtain ⟨p1, p2, p3⟩ := lwSplitLoops_props m Δ.solid r hr
  refine ⟨h2, fun u v huv => ?_, p1⟩
  rw [show ({ Δ with solid := r.2, coeff := r.1 * Δ.coeff } : LGraph E' I').XBetween u v ↔
    Δ.XBetween u v from Iff.rfl, h3 u v huv]
  constructor
  · rintro ⟨e, he, hne, h⟩
    exact ⟨e, p3 e he hne, hne, h⟩
  · rintro ⟨e, he, hne, h⟩
    exact ⟨e, p2 e he hne, hne, h⟩

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem LGraph.merge_SBetween_iff (Δ : LGraph E I) (u v : Δ.ExtCls ⊕ Δ.IntCls) (huv : u ≠ v) :
    Δ.merge.SBetween u v ↔ ∃ s ∈ Δ.solid,
      (Δ.vmap s.src = u ∧ Δ.vmap s.dst = v) ∨ (Δ.vmap s.src = v ∧ Δ.vmap s.dst = u) := by
  constructor
  · rintro ⟨e, he, _, h⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s.map Δ.vmap, List.mem_map_of_mem hs, ?_, h⟩
    intro hh
    apply huv
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hh
    · rw [← h1, ← h2]; exact hh.symm

private theorem LGraph.merge_XBetween_iff (Δ : LGraph E I) (u v : Δ.ExtCls ⊕ Δ.IntCls) :
    Δ.merge.XBetween u v ↔ ∃ e ∈ Δ.dotted, e.eq = false ∧
      ((Δ.vmap e.x = u ∧ Δ.vmap e.y = v) ∨ (Δ.vmap e.x = v ∧ Δ.vmap e.y = u)) := by
  constructor
  · rintro ⟨e, he, heq, h⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨he0, hq⟩ := List.mem_filter.1 he0
    exact ⟨e0, he0, by simpa using hq, h⟩
  · rintro ⟨e, he, heq, h⟩
    exact ⟨e.map Δ.vmap, List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp [heq]⟩, rfl⟩, heq, h⟩

private theorem lwPair_transfer {α β : Type*} (f : α → β) {a b x y : α} {u v : β}
    (h : (a = x ∧ b = y) ∨ (a = y ∧ b = x)) (h' : (f x = u ∧ f y = v) ∨ (f x = v ∧ f y = u)) :
    (f a = u ∧ f b = v) ∨ (f a = v ∧ f b = u) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [*]

/-- The merged graph of a term `Dot · Γ` has no dotted edge and satisfies (iii) of `defnlvl0`: two
different vertices are joined by a `×`-dotted edge iff they are joined by a solid edge. -/
private theorem LGraph.withDots_merge_conditions (Γ : LGraph E I) (c : ℤ × List (DEdge (E ⊕ I)))
    (hc : c ∈ Γ.dotChoices) :
    (∀ e ∈ (Γ.withDots c).merge.dotted, e.eq = false) ∧
    (∀ u v, u ≠ v → ((Γ.withDots c).merge.XBetween u v ↔ (Γ.withDots c).merge.SBetween u v)) := by
  set Δ := Γ.withDots c with hΔ
  have hdot : Δ.dotted = Γ.dotBase ++ c.2 := rfl
  have hsolid : Δ.solid = Γ.solid := rfl
  refine ⟨?_, fun u v huv => ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨_, hq⟩ := List.mem_filter.1 he0
    have : e0.eq = false := by simpa using hq
    exact this
  rw [Δ.merge_XBetween_iff, Δ.merge_SBetween_iff u v huv]
  constructor
  · rintro ⟨e, he, heq, h⟩
    rw [hdot, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨he0, hb⟩ := List.mem_filter.1 he
      have hS : Γ.SBetween e.x e.y := by
        by_contra hn
        have : Γ.isB e = true := by simp [LGraph.isB, heq, hn]
        simp [this] at hb
      obtain ⟨s, hs, hne, hs'⟩ := hS
      exact ⟨s, hs, lwPair_transfer Δ.vmap hs' h⟩
    · obtain ⟨a, ha, o, ho, heo⟩ := lwCombineAtoms_mem_edge _ c hc e he
      simp only [LGraph.dotAtoms, List.mem_append, List.mem_map] at ha
      rcases ha with ⟨p, hp, rfl⟩ | ⟨e', he', rfl⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl
        · simp only [List.mem_singleton] at heo
          subst heo
          simp at heq
        · simp only [List.mem_singleton] at heo
          subst heo
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (lwMem_of_mem_dedupPairs hp)
          exact ⟨s, (List.mem_filter.1 hs).1, h⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl
        · simp at heo
        · simp only [List.mem_singleton] at heo
          subst heo
          simp at heq
  · rintro ⟨s, hs, h⟩
    have hsne : s.src ≠ s.dst := by
      intro hh
      apply huv
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hh]
      · rw [← h1, ← h2, hh]
    by_cases hX : Γ.XBetween s.src s.dst
    · obtain ⟨e0, he0, heq0, he0'⟩ := hX
      have hS : Γ.SBetween e0.x e0.y := by
        refine ⟨s, hs, hsne, ?_⟩
        rcases he0' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      have hb : e0 ∈ Γ.dotBase := List.mem_filter.2 ⟨he0, by simp [LGraph.isB, heq0, hS]⟩
      refine ⟨e0, by rw [hdot]; exact List.mem_append.2 (Or.inl hb), heq0, ?_⟩
      have h1 : (s.src = e0.x ∧ s.dst = e0.y) ∨ (s.src = e0.y ∧ s.dst = e0.x) := by
        rcases he0' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact h
      · rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr ⟨by rw [← h2]; exact h4, by rw [← h1]; exact h3⟩
        · exact Or.inl ⟨by rw [← h2]; exact h4, by rw [← h1]; exact h3⟩
    · have hmem : (s.src, s.dst) ∈ ((Γ.solid.filter fun e =>
          decide (e.src ≠ e.dst ∧ ¬ Γ.XBetween e.src e.dst)).map fun e => (e.src, e.dst)) :=
        List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simp [hsne, hX]⟩, rfl⟩
      obtain ⟨q, hq, hqs⟩ := lwExists_mem_dedupPairs hmem
      have hqs' := (lwSamePair_iff _ _).1 hqs
      have hatom : [(1, [⟨true, q.1, q.2⟩]), (1, [⟨false, q.1, q.2⟩])] ∈ Γ.dotAtoms := by
        simp only [LGraph.dotAtoms, List.mem_append, List.mem_map]
        exact Or.inl ⟨q, hq, rfl⟩
      obtain ⟨o, ho, hoc⟩ := lwCombineAtoms_mem_option _ c hc _ hatom
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl
      · have hedge : (⟨true, q.1, q.2⟩ : DEdge (E ⊕ I)) ∈ c.2 := hoc _ (by simp)
        have hv : Δ.vmap q.1 = Δ.vmap q.2 :=
          Δ.vmap_eq_of_rel ⟨⟨true, q.1, q.2⟩, by rw [hdot]; exact List.mem_append.2 (Or.inr hedge),
            rfl, Or.inl ⟨rfl, rfl⟩⟩
        exfalso
        apply huv
        rcases hqs' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at hv
          rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [← h3, ← h4]; exact hv
          · rw [← h3, ← h4]; exact hv.symm
        · rw [h1, h2] at hv
          rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [← h3, ← h4]; exact hv.symm
          · rw [← h3, ← h4]; exact hv
      · have hedge : (⟨false, q.1, q.2⟩ : DEdge (E ⊕ I)) ∈ c.2 := hoc _ (by simp)
        refine ⟨⟨false, q.1, q.2⟩, by rw [hdot]; exact List.mem_append.2 (Or.inr hedge), rfl, ?_⟩
        exact lwPair_transfer Δ.vmap (a := q.1) (b := q.2) hqs' h

/-- **The terms of the partition are normal graphs** (`dot-def`): every term of the
linear combination `LGraph.partition m Γ` satisfies `defnlvl0` (ii)-(iv). -/
theorem LGraph.partition_normal (m : ℂ) (Γ : LGraph E I) :
    ∀ P ∈ Γ.partition m, P.g.Normal := by
  intro P hP
  classical
  unfold LGraph.partition LGraph.partitionTerms at hP
  obtain ⟨Δ, hΔ, hPΔ⟩ := List.mem_flatMap.1 hP
  obtain ⟨hΔ, _⟩ := List.mem_filter.1 hΔ
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hΔ
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hPΔ
  obtain ⟨h2, h3⟩ := Γ.withDots_merge_conditions c hc
  exact LGraph.normal_of_split m _ h2 h3 g hg

end PartitionNormal

/-! ## 12. Scaling size and scaling order (`def scaling`; `def scaling order`)

The scaling size and order of a **normal** graph are functions of its counters (`LGraph.counters`,
`RBM.Graph.Counters`).  For a general graph the paper defines them through the dotted edge
partition: `size = max_k size(Γ_k)` and `ord = min_k ord(Γ_k)` over the normal graphs `Γ_k` of
`LGraph.partition` (`(eq_defsizemax)` (7.17)).  When the partition is empty (all terms inconsistent:
the graph is `0`) the maximum is `0` and the minimum is `⊤`.  `Ψ_t` is a
parameter `Ψ`; `W`, `d`, `L` are the model parameters.  The record needs no new field: the counters
`LGraph.counters` are all that `size` and `ord` read. -/

section Scaling

/-- `(eq_defsize)` (7.16): `size(Γ) = (L^d)^{n_M} Ψ^{n_S} W^{-d (n_W - n_V)}`, an integer power
of `W`. -/
def Counters.scalingSize (c : Counters) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  ((L : ℝ) ^ d) ^ c.nM * Ψ ^ c.nS * (W : ℝ) ^ (-(d : ℤ) * ((c.nW : ℤ) - (c.nV : ℤ)))

/-- The identity after `def scaling order`: `size(Γ) = (L^d)^{n_M} Ψ^{ord(Γ)} (W^d Ψ²)^{n_V - n_W}`. -/
theorem Counters.scalingSize_eq (c : Counters) {Ψ : ℝ} (W d L : ℕ) (hΨ : Ψ ≠ 0) :
    c.scalingSize Ψ W d L =
      ((L : ℝ) ^ d) ^ c.nM * Ψ ^ (ord c) * ((W : ℝ) ^ d * Ψ ^ 2) ^ ((c.nV : ℤ) - c.nW) := by
  unfold Counters.scalingSize ord
  set a : ℤ := (c.nW : ℤ) - c.nV with ha
  have h1 : ((c.nV : ℤ) - c.nW) = -a := by omega
  have e1 : ((W : ℝ) ^ d) ^ (-a) = (W : ℝ) ^ (-(d : ℤ) * a) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
  have e2 : (Ψ ^ 2) ^ (-a) = Ψ ^ (-(2 * a)) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have e3 : Ψ ^ ((c.nS : ℤ) + 2 * a) * Ψ ^ (-(2 * a)) = Ψ ^ c.nS := by
    rw [← zpow_add₀ hΨ, ← zpow_natCast]; congr 1; ring
  rw [h1, mul_zpow, e1, e2]
  calc _ = ((L : ℝ) ^ d) ^ c.nM * (Ψ ^ ((c.nS : ℤ) + 2 * a) * Ψ ^ (-(2 * a))) *
        (W : ℝ) ^ (-(d : ℤ) * a) := by rw [e3]
    _ = _ := by ring

/-- The window `Ψ ≥ W^{-d/2}` (Definition 7.10) is `W^d Ψ² ≥ 1`. -/
theorem one_le_pow_mul_sq_iff {Ψ : ℝ} (W d : ℕ) (hW : 0 < (W : ℝ)) (hΨ : 0 ≤ Ψ) :
    (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ ↔ 1 ≤ (W : ℝ) ^ d * Ψ ^ 2 := by
  have hpos : 0 < (W : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos hW _
  have hsq : ((W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = ((W : ℝ) ^ d)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le,
      show (-(d : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -(d : ℝ) by push_cast; ring,
      Real.rpow_neg hW.le, Real.rpow_natCast]
  rw [← pow_le_pow_iff_left₀ hpos.le hΨ (two_ne_zero), hsq, inv_le_iff_one_le_mul₀' (by positivity)]

section Graphs

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The scaling size of a normal graph (`def scaling`). -/
def LGraph.scalingSize (Γ : LGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  Γ.counters.scalingSize Ψ W d L

/-- The scaling order of a normal graph (`def scaling order`), `(eq:ordG)`: the
`RBM.Graph.ord` of the counters. -/
def LGraph.scalingOrder (Γ : LGraph E I) : ℤ := ord Γ.counters

end Graphs

end Scaling

/-! ## 13. Adjacency

The adjacency relation `LGraph.adj` unfolds to the waved and `=`-dotted edges. -/

section Union

private theorem LGraph.adj_iff {E I : Type*} (Γ : LGraph E I) [DecidableEq E] [DecidableEq I] (u v : E ⊕ I) :
    Γ.adj u v = true ↔
      (∃ e ∈ Γ.waved, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) ∨
      (∃ e ∈ Γ.dotted, e.eq = true ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) := by
  simp [LGraph.adj, List.any_eq_true]

end Union

/-! ## 14. Counters are invariant under a bijective relabeling -/

section RelabelCounters

variable {E E' I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

private theorem lwAdj_relabel (Γ : LGraph E I) (φ : E ⊕ I ≃ E' ⊕ I') (u v : E ⊕ I) :
    (Γ.relabel φ).adj (φ u) (φ v) = Γ.adj u v := by
  rw [Bool.eq_iff_iff, LGraph.adj_iff, LGraph.adj_iff]
  simp [LGraph.relabel, WEdge.map, DEdge.map]

private theorem lwStep_relabel (Γ : LGraph E I) (φ : E ⊕ I ≃ E' ⊕ I') (s : Finset (E ⊕ I)) :
    (Γ.relabel φ).step (s.map φ.toEmbedding) = (Γ.step s).map φ.toEmbedding := by
  ext w'
  obtain ⟨w, rfl⟩ := φ.surjective w'
  simp only [LGraph.step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Equiv.symm_apply_apply]
  constructor
  · rintro (h | ⟨v', hv', hadj⟩)
    · exact Or.inl h
    · refine Or.inr ⟨φ.symm v', hv', ?_⟩
      rw [← lwAdj_relabel Γ φ, Equiv.apply_symm_apply]
      exact hadj
  · rintro (h | ⟨v, hv, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨φ v, by simpa using hv, by rw [lwAdj_relabel]; exact hadj⟩

private theorem lwIterate_relabel (Γ : LGraph E I) (φ : E ⊕ I ≃ E' ⊕ I') (n : ℕ) :
    ∀ s : Finset (E ⊕ I), (Γ.relabel φ).step^[n] (s.map φ.toEmbedding) =
      (Γ.step^[n] s).map φ.toEmbedding := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, lwStep_relabel, ih]

private theorem lwMol_relabel (Γ : LGraph E I) (φ : E ⊕ I ≃ E' ⊕ I') (v : E ⊕ I) :
    (Γ.relabel φ).mol (φ v) = (Γ.mol v).map φ.toEmbedding := by
  unfold LGraph.mol
  have h1 : ({φ v} : Finset (E' ⊕ I')) = ({v} : Finset (E ⊕ I)).map φ.toEmbedding := by simp
  rw [show Fintype.card (E' ⊕ I') = Fintype.card (E ⊕ I) from (Fintype.card_congr φ).symm, h1,
    lwIterate_relabel]

/-- **The counters are invariant under a relabeling by a bijection** of the vertices that keeps the
external and the internal vertices apart. -/
theorem LGraph.counters_relabel_equiv (Γ : LGraph E I) (φ : E ⊕ I ≃ E' ⊕ I')
    (hφ : ∀ v, (φ v).isRight = v.isRight) :
    (Γ.relabel φ).nS = Γ.nS ∧ (Γ.relabel φ).nW = Γ.nW ∧ (Γ.relabel φ).nV = Γ.nV ∧
      (Γ.relabel φ).nM = Γ.nM := by
  refine ⟨by simp [LGraph.nS, LGraph.relabel], by simp [LGraph.nW, LGraph.relabel], ?_, ?_⟩
  · unfold LGraph.nV
    exact (Fintype.card_congr
      (Equiv.sumIsRight.symm.trans ((Equiv.subtypeEquiv φ fun v => by simp [hφ]).trans
        Equiv.sumIsRight))).symm
  · unfold LGraph.nM
    have hP : ∀ v, (∀ w ∈ (Γ.relabel φ).mol (φ v), w.isRight = true) ↔ ∀ w ∈ Γ.mol v, w.isRight = true := by
      intro v
      rw [lwMol_relabel]
      constructor
      · intro h w hw
        have := h (φ w) (Finset.mem_map_of_mem _ hw)
        rwa [hφ] at this
      · intro h w' hw'
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hw'
        rw [Equiv.coe_toEmbedding, hφ]
        exact h w hw
    have himg : (Finset.univ.filter fun v' : E' ⊕ I' => ∀ w ∈ (Γ.relabel φ).mol v', w.isRight = true).image
        (Γ.relabel φ).mol =
        ((Finset.univ.filter fun v : E ⊕ I => ∀ w ∈ Γ.mol v, w.isRight = true).image Γ.mol).image
          (Finset.map φ.toEmbedding) := by
      ext T
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v', hv', rfl⟩
        obtain ⟨v, rfl⟩ := φ.surjective v'
        exact ⟨Γ.mol v, ⟨v, (hP v).1 hv', rfl⟩, (lwMol_relabel Γ φ v).symm⟩
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨φ v, (hP v).2 hv, lwMol_relabel Γ φ v⟩
    rw [himg, Finset.card_image_of_injective _ (Finset.map_injective _)]

end RelabelCounters

/-! ## 15. Graphs without `=`-dotted edges

For a graph whose dotted edges are all `×`-dotted, the classes of the equivalence relation
generated by the `=`-dotted edges are singletons (`lwCls_eq_iff`) and the merge map keeps external
and internal vertices apart (`lwVmap_isRight`). -/

section NormalAgree

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem lwCls_eq_iff (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (u v : E ⊕ I) :
    Γ.cls u = Γ.cls v ↔ u = v := by
  constructor
  · intro huv
    have h' : Relation.EqvGen Γ.EqRel u v := Quotient.exact huv
    clear huv
    induction h' with
    | rel a b hr =>
      obtain ⟨e, he, heq, _⟩ := hr
      rw [h e he] at heq
      exact absurd heq (by simp)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · rintro rfl
    rfl

private theorem lwVmap_isRight (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (v : E ⊕ I) :
    (Γ.vmap v).isRight = v.isRight := by
  rcases v with a | b
  · rw [LGraph.vmap_inl]; rfl
  · have hq : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b)) := by
      rintro ⟨a, ha⟩
      exact absurd ((lwCls_eq_iff Γ h _ _).1 ha) (by simp)
    rw [LGraph.vmap_inr_int Γ b hq]
    rfl

end NormalAgree

end RBM.Graph
