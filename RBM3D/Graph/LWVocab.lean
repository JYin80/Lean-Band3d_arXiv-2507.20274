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
# LW-03: the graph vocabulary of the light-weight layer (T2050)

The vocabulary of `paper/tex/7_8_light_weight.tex:116-287` (cited `7_8:line`) on the record
representation `LGraph E I` chosen in DECISIONS §24 (representation A): `E` the external vertices
(labels fixed), `I` the internal vertices (labels summed), edges of three kinds and a coefficient.

## Copied verbatim from the probe (`git show eeda441:RBM3D/Probe/T2040Graphs.lean`)

Lines 54-281 (section 1: `LData`, `SEdge`, `WEdge`, `DEdge`, `LGraph`, `LGraph.val`, molecules,
counters, the examples `p2Graph`, `figGraph`) and lines 331-432 (section 3: `NGraph`, `IsNested`,
`NoGhost`, `GhostOK`, the example `figAux`).  Nothing else of the probe is used.

## Added here (sections 4-15), with the field or function that represents each definition

* `def_graph1` (`7_8:116-152`): no new field is needed.  Added: `SEdge.IsWeight`, `IsLightWeight`,
  `charge`, `IntEnds` (internal edges), `LGraph.DotWF` ("at most one dotted edge per pair", not
  enforced by the record).
* `ValG` (`7_8:159-164`): `LGraph.val`; a linear combination is a list of `PGraph E` (a graph with
  its own vertex types and the map `ext` of the original external vertices), `LComb.val`.
* molecules `def_poly` (`7_8:171-188`): `mol` is the connected component of the waved and
  `=`-dotted edges (`mem_mol_iff`), `Mol`, `molOf`, `IsExtMol`, `molSolid` (the molecular graph),
  `nM_eq_card` (`n_M` counts the internal molecules).
* normal graphs `defnlvl0` (`7_8:196-210`): the predicate `LGraph.Normal`.
* the dotted edge partition `dot-def` (`7_8:214-225`): `dotChoices` (expansion of the dotted edges),
  `withDots`, `merge` (vertices joined by `=`-dotted edges), `splitWeights` (weights to
  light-weights and a coefficient `m`), `partition : List (PGraph E)`; `val_eq_partition` (the
  value is the value of the combination), `partition_normal` (every term is a normal graph),
  `partition_of_normal`.
* scaling size `def scaling` (`7_8:232-255`) and scaling order `def scaling order` (`7_8:270-284`):
  `Counters.scalingSize`, `LGraph.scalingSize`, `scalingOrder` for normal graphs (the merged
  `RBM.Graph.ord`), `scalingSizeG`, `scalingOrderG` for general graphs (maximum / minimum over the
  partition), `scalingSize_eq`, `scalingSize_le` (`7_8:274-277`).
* basic lemmas: `val_of_isEmpty`, `val_relabel_equiv`, `val_map_equiv`, `disjUnion`
  (`val_disjUnion`, `nS/nW/nV/nM_disjUnion`, `ord_disjUnion`), `counters_relabel_equiv`.
* compiled instances (section 15): the two probe examples with counters and `ord` by `decide`, a
  normal graph with a `×`-dotted edge, the partition of `∑_a G_{xa} Ḡ_{xa}` at concrete data.

Reused from the merged `RBM3D/Graph/ScalingOrder.lean`: `RBM.Graph.Counters`, `RBM.Graph.ord`.
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

/-- A solid edge (`def_graph1`, `7_8:121-127`): blue (`σ = true`, charge `+`, `G_{xy}`) or red
(`σ = false`, `Ḡ_{xy}`), with (`circ`) or without a circle (`(G-M)_{xy}`); `src = dst` is a weight
(a self-loop). -/
structure SEdge (V : Type*) where
  σ : Bool
  circ : Bool
  src : V
  dst : V

/-- A waved edge (`7_8:134-139`): black `S_{xy}` (`col = false`) or coloured `S^±_{xy}`. -/
structure WEdge (V : Type*) where
  col : Bool
  σ : Bool
  x : V
  y : V

/-- A dotted edge (`7_8:141`): `1_{x=y}` (`eq = true`) or the `×`-dotted `1_{x≠y}`. -/
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

/-- **`ValG`** (`7_8:159-164`): the product of the edge factors and the coefficient, summed over the
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

/-- `x` and `y` are joined by a waved edge or a dotted `=` edge (`def_poly`, `7_8:172`). -/
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

/-- The counters of `def scaling` / `def scaling order` in the merged `RBM.Graph.Counters`
(`nlw`, `ndv` are proof bookkeeping of `lem_scalingorder`, not invariants of the graph). -/
def LGraph.counters (Γ : LGraph E I) : Counters := ⟨Γ.nS, Γ.nW, Γ.nV, Γ.nM, 0, 0⟩

end Counters

section Examples

/-- `(eq:p=2graph)` (`7_8:507`): `E|f_xy|²` as a graph.  External `x, y` = `inl 0, inl 1`; internal
`α₁, β₁, α₂, β₂ = inr 0 .. inr 3`; blue `Ǧ_{β₁β₁} G_{xα₁} G_{α₁y}`, red likewise, waved
`S_{α₁β₁}`, `S_{α₂β₂}`, and the `×`-dotted edges of `1_{α_i ∉ {x,y}}`. -/
def p2Graph : LGraph (Fin 2) (Fin 4) where
  solid := [⟨true, true, .inr 1, .inr 1⟩, ⟨true, false, .inl 0, .inr 0⟩, ⟨true, false, .inr 0, .inl 1⟩,
            ⟨false, true, .inr 3, .inr 3⟩, ⟨false, false, .inl 0, .inr 2⟩, ⟨false, false, .inr 2, .inl 1⟩]
  waved := [⟨false, true, .inr 0, .inr 1⟩, ⟨false, true, .inr 2, .inr 3⟩]
  dotted := [⟨false, .inr 0, .inl 0⟩, ⟨false, .inr 0, .inl 1⟩, ⟨false, .inr 2, .inl 0⟩,
             ⟨false, .inr 2, .inl 1⟩]
  coeff := 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value of `p2Graph`, unfolded by `simp` to the explicit four-fold sum of `(eq:p=2graph)`. -/
theorem p2Graph_val (D : LData ι) (x y : ι) :
    p2Graph.val D ![x, y] =
      ∑ a₁, ∑ b₁, ∑ a₂, ∑ b₂,
        (if a₁ ≠ x ∧ a₁ ≠ y ∧ a₂ ≠ x ∧ a₂ ≠ y then 1 else 0) *
        (D.S a₁ b₁ * D.S a₂ b₂ *
         ((D.G b₁ b₁ - D.M b₁ b₁) * D.G x a₁ * D.G a₁ y) *
         star ((D.G b₂ b₂ - D.M b₂ b₂) * D.G x a₂ * D.G a₂ y)) := by
  unfold LGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero]
  simp [p2Graph, LGraph.term, SEdge.val, WEdge.val, DEdge.val]
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
  by_cases h1 : a₂ = y <;> by_cases h2 : a₂ = x <;> by_cases h3 : a₁ = y <;> by_cases h4 : a₁ = x <;>
    (simp [h1, h2, h3, h4]; try exact Finset.sum_congr rfl fun b₂ _ => by ring)

/-- `f_{xy}(G) = Σ_{α∉{x,y}} Σ_β S_{αβ} Ǧ_{ββ} G_{xα} G_{αy}` (`(fxyG_sum)`, `7_8:31-34`). -/
def fxyVal (D : LData ι) (x y : ι) : ℂ :=
  ∑ α, if α = x ∨ α = y then 0 else ∑ β, D.S α β * (D.G β β - D.M β β) * D.G x α * D.G α y

/-- **The graph `p2Graph` has the value `|f_{xy}|²`** (for the real variance matrix `S`). -/
theorem p2Graph_val_eq (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (x y : ι) :
    p2Graph.val D ![x, y] = fxyVal D x y * star (fxyVal D x y) := by
  rw [p2Graph_val]
  unfold fxyVal
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  by_cases h : a₁ = x ∨ a₁ = y ∨ a₂ = x ∨ a₂ = y
  · rcases h with h | h | h | h <;> simp [h]
  · push Not at h
    simp only [ne_eq, h.1, h.2.1, h.2.2.1, h.2.2.2, not_false_eq_true, and_self, ite_true, one_mul,
      or_self, ite_false, star_sum, Finset.sum_mul_sum, star_mul']
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    rw [hS]
    ring

/-- The counters of `p2Graph` (`def scaling`: `n_S = 3p`, `n_W = p`, `n_V = 2p`, `n_M = p` at `p = 2`)
and its scaling order `ord = p = 2` (`(eq:initial_scaling)`, `B:201`), computed by `decide`. -/
theorem p2Graph_counters :
    p2Graph.nS = 6 ∧ p2Graph.nW = 2 ∧ p2Graph.nV = 4 ∧ p2Graph.nM = 2 := by decide

theorem p2Graph_ord : ord p2Graph.counters = 2 := by
  have h := p2Graph_counters
  simp only [LGraph.counters, ord, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num

/-- The graph `𝒢` of the left panel of `fig:p=2expansion` (`7_8:568-677`), obtained from
`(eq:p=2graph)` by two weight expansions: external `x, y`; internal `α₁, β₁, γ₁, α₂, β₂, γ₂ =
inr 0 .. inr 5`; the blue edges `x→α₁`, `α₁→β₂`, `γ₂→y`, `β₁→γ₁`, the red edges `x→γ₁`, `β₁→α₂`,
`α₂→y`, `γ₂→β₂`; waved edges `α₁β₁`, `β₁γ₁`, `α₂β₂`, `β₂γ₂`; one `×`-dotted edge for each solid edge
(a normal graph, `defnlvl0`).  The coefficient (a monomial in `m, m̄`) does not enter the counters. -/
def figGraph : LGraph (Fin 2) (Fin 6) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨true, false, .inr 0, .inr 4⟩, ⟨true, false, .inr 5, .inl 1⟩,
            ⟨true, false, .inr 1, .inr 2⟩, ⟨false, false, .inl 0, .inr 2⟩, ⟨false, false, .inr 1, .inr 3⟩,
            ⟨false, false, .inr 3, .inl 1⟩, ⟨false, false, .inr 5, .inr 4⟩]
  waved := [⟨false, true, .inr 0, .inr 1⟩, ⟨false, true, .inr 1, .inr 2⟩, ⟨false, true, .inr 3, .inr 4⟩,
            ⟨false, true, .inr 4, .inr 5⟩]
  dotted := [⟨false, .inl 0, .inr 0⟩, ⟨false, .inr 0, .inr 4⟩, ⟨false, .inr 5, .inl 1⟩,
             ⟨false, .inr 1, .inr 2⟩, ⟨false, .inl 0, .inr 2⟩, ⟨false, .inr 1, .inr 3⟩,
             ⟨false, .inr 3, .inl 1⟩, ⟨false, .inr 5, .inr 4⟩]
  coeff := 1

/-- `n_S = 8`, `n_W = 4`, `n_V = 6`, `n_M = 2` (the molecules `{α₁,β₁,γ₁}`, `{α₂,β₂,γ₂}`) and
`ord = 8 + 2 (4 - 6) = 4 = 2p` at `p = 2`: the bound `(eq:sizeGammamu)` is tight here. -/
theorem figGraph_counters :
    figGraph.nS = 8 ∧ figGraph.nW = 4 ∧ figGraph.nV = 6 ∧ figGraph.nM = 2 := by decide

theorem figGraph_ord : ord figGraph.counters = 4 := by
  have h := figGraph_counters
  simp only [LGraph.counters, ord, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num

/-- **The value of `figGraph`, unfolded** (`ValG`, `7_8:159`): the six-fold sum over
`α₁, β₁, γ₁, α₂, β₂, γ₂` of the product of the eight `×`-dotted conditions, the eight `G`, `Ḡ` factors and
the four waved factors `S_{α₁β₁} S_{β₁γ₁} S_{α₂β₂} S_{β₂γ₂}`. -/
theorem figGraph_val (D : LData ι) (x y : ι) :
    figGraph.val D ![x, y] =
      ∑ a₁, ∑ b₁, ∑ c₁, ∑ a₂, ∑ b₂, ∑ c₂,
        (if x = a₁ then 0 else 1) * (if a₁ = b₂ then 0 else 1) * (if c₂ = y then 0 else 1) *
        (if b₁ = c₁ then 0 else 1) * (if x = c₁ then 0 else 1) * (if b₁ = a₂ then 0 else 1) *
        (if a₂ = y then 0 else 1) * (if c₂ = b₂ then 0 else 1) *
        (D.G x a₁ * D.G a₁ b₂ * D.G c₂ y * D.G b₁ c₁ * star (D.G x c₁) * star (D.G b₁ a₂) *
          star (D.G a₂ y) * star (D.G c₂ b₂) * (D.S a₁ b₁ * D.S b₁ c₁ * D.S a₂ b₂ * D.S b₂ c₂)) := by
  unfold LGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero]
  simp [figGraph, LGraph.term, SEdge.val, WEdge.val, DEdge.val]
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun c₁ _ =>
    Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun c₂ _ => ?_
  split_ifs <;> ring

end Examples

/-! ## 3. Nested graphs (`lem:Anp_key`, `lem:Anp_key_gh`, `7_8:960-1077`)

The auxiliary graph of `def_auxgraph` has the block-level vertices `[a_i], [b_i]` (external) and
`[α_j]` (internal); its edges are solid (a factor `ξ`) or ghost (the factor `1`, `7_8:1015`).  The
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

instance (i : Fin p) : Decidable (Γ.WalkOK i) := by unfold WalkOK; infer_instance

/-- The path properties (1)-(3) of `lem:Anp_key` (`7_8:968-979`), no self-loops: (1) `p`
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

/-- The ghost condition of `lem:Anp_key_gh` (`7_8:1042`): each path has at most one ghost edge, and it
is an ending edge (the first or the last step). -/
def GhostOK : Prop :=
  ∀ i, (((Γ.path i).filter fun st => (Γ.es.get st.1).ghost).length ≤ 1) ∧
    ∀ st ∈ Γ.path i, (Γ.es.get st.1).ghost = true → (Γ.path i).head? = some st ∨ (Γ.path i).getLast? = some st

/-- The number of solid (non-ghost) edges. -/
def nSolid : ℕ := (Γ.es.filter fun e => !e.ghost).length

/-- The path `i` has no ghost edge. -/
def noGhostPath (i : Fin p) : Bool := (Γ.path i).all fun st => !(Γ.es.get st.1).ghost

/-- `n_ngh`: the number of paths without a ghost edge (`7_8:1047`). -/
def nngh : ℕ := (Finset.univ.filter fun i : Fin p => Γ.noGhostPath i = true).card

/-- `ord(𝒢) = #solid edges - 2 #internal vertices` (`(eq:ordGaux)`, `7_8:902`): the merged
`RBM.Graph.ord` with `n_W = 0` and `n_V = q`. -/
def ordN : ℤ := ord ⟨Γ.nSolid, 0, q, 0, 0, 0⟩

/-- The value (`ValG` for the auxiliary graph): the edge `{u, v}` carries `ξ` of its labels, a ghost
edge `1`; internal labels are summed, `a`, `b` are the external labels. -/
def val {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (a b : Fin p → ι) : ℝ :=
  ∑ ℓ : Fin q → ι, (Γ.es.map fun e =>
    if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod

end NGraph

/-- The auxiliary graph of the left panel of `fig:p=2expansion` (`7_8:626-647`, middle panel `𝒢₁`):
`p = q = 2`, the vertices `[x], [y]` (both `a_i = [a]`, `b_i = [b]`), `ℳ₁, ℳ₂`; the six solid edges
`x ℳ₁` (twice), `ℳ₁ ℳ₂` (twice), `ℳ₂ y` (twice); the two paths `x → ℳ₁ → ℳ₂ → y` (blue and red). -/
def figAux : NGraph 2 2 where
  es := [⟨false, .inl (.inl 0), .inr 0⟩, ⟨false, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inr 1⟩,
         ⟨false, .inr 0, .inr 1⟩, ⟨false, .inr 1, .inl (.inr 0)⟩, ⟨false, .inr 1, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (2, .inr 1), (4, .inl (.inr 0))]
    else [(1, .inr 0), (3, .inr 1), (5, .inl (.inr 1))]

instance : Decidable figAux.IsNested := by unfold NGraph.IsNested; infer_instance

instance : Decidable figAux.NoGhost := by unfold NGraph.NoGhost; infer_instance

theorem figAux_nested : figAux.IsNested ∧ figAux.NoGhost := by
  decide +kernel

/-- `ord(𝒢₁^{aux}) = 6 - 2·2 = 2` (`(eq:ordGaux)`): `ord(𝒢) - ord(𝒢^{aux}) = 4 - 2 = 2`, the two
short edges inside the molecules (`GtoAG`: the factor `Ψ_t²`). -/
theorem figAux_ord : figAux.ordN = 2 := by
  decide +kernel



/-! ## 4. Added vocabulary (T2050): `def_graph1` beyond the probe

The record of section 1 already carries every edge kind of `def_graph1` (`7_8:116-152`): solid edges
`G`, `Ḡ`, `G - M`, `\overline{G - M}` (`SEdge`, the flags `σ` and `circ`), weights and light-weights
(`SEdge` with `src = dst`), waved edges `S`, `S^±` (`WEdge`), dotted and `×`-dotted edges (`DEdge`),
the coefficient (`coeff`).  Fields the probe lacks and this file adds: none for `def_graph1`
itself; only predicates (loops, weights, charges, internal edges, well-formed dotted edges) and the
packing of graphs with their own internal vertex types, which a linear combination needs. -/

section Edges

variable {V W : Type*}

/-- Relabelling of the end vertices of a solid edge. -/
def SEdge.map (f : V → W) (e : SEdge V) : SEdge W := ⟨e.σ, e.circ, f e.src, f e.dst⟩

/-- Relabelling of the end vertices of a waved edge. -/
def WEdge.map (f : V → W) (e : WEdge V) : WEdge W := ⟨e.col, e.σ, f e.x, f e.y⟩

/-- Relabelling of the end vertices of a dotted edge. -/
def DEdge.map (f : V → W) (e : DEdge V) : DEdge W := ⟨e.eq, f e.x, f e.y⟩

/-- A weight: a self-loop without circle, `G_{xx}` or `Ḡ_{xx}` (`7_8:127`, "call `G_{xx}` and `Ḡ_{xx}`
blue and red weights"). -/
def SEdge.IsWeight (e : SEdge V) : Prop := e.src = e.dst ∧ e.circ = false

/-- A light-weight: a self-loop with circle, `(G-M)_{xx}` or its conjugate (`7_8:127`). -/
def SEdge.IsLightWeight (e : SEdge V) : Prop := e.src = e.dst ∧ e.circ = true

/-- The charge of a solid edge: `+1` blue, `-1` red (`7_8:133`). -/
def SEdge.charge (e : SEdge V) : ℤ := if e.σ then 1 else -1

/-- An edge between two internal vertices is *internal*; an edge with at least one end at an external
vertex is *external* (`7_8:151`).  The vertex `inr i` is internal, `inl a` external. -/
def IntEnds {E I : Type*} (u v : E ⊕ I) : Prop := u.isRight = true ∧ v.isRight = true

/-- `7_8:141` "There is at most one dotted or `×`-dotted edge between every pair of vertices": the
pairs of the dotted edges are pairwise distinct as unordered pairs, and no dotted edge is a loop.  The
record does not enforce it; `LGraph.val` and the counters do not need it. -/
def LGraph.DotWF {E I : Type*} (Γ : LGraph E I) : Prop :=
  (Γ.dotted.map fun e => Sym2.mk e.x e.y).Nodup ∧ ∀ e ∈ Γ.dotted, e.x ≠ e.y

instance {E I : Type*} [DecidableEq E] [DecidableEq I] (Γ : LGraph E I) : Decidable Γ.DotWF := by
  unfold LGraph.DotWF; infer_instance

end Edges

section Relabel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E E' I I' V W : Type*}

private theorem SEdge.val_map (D : LData ι) (f : V → W) (ℓ : W → ι) (e : SEdge V) :
    (e.map f).val D ℓ = e.val D (ℓ ∘ f) := rfl

private theorem WEdge.val_map (D : LData ι) (f : V → W) (ℓ : W → ι) (e : WEdge V) :
    (e.map f).val D ℓ = e.val D (ℓ ∘ f) := rfl

private theorem DEdge.val_map (f : V → W) (ℓ : W → ι) (e : DEdge V) :
    (e.map f).val ℓ = e.val (ℓ ∘ f) := rfl

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

/-! ## 5. Molecules (`def_poly`, `7_8:171-188`)

"Two vertices belong to the same molecule if and only if they are connected by a path of dotted and
waved edges."  The probe's `LGraph.mol` computes the closure by `|E ⊕ I|` neighbourhood steps;
`mem_mol_iff` shows that it is the connected component in the graph `molGraph` of the waved edges
and the `=`-dotted edges (the `×`-dotted edges do not connect).  The record needs no new field: the
molecules are computed from `waved` and `dotted`. -/

section Mol

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem LGraph.adj_comm (Γ : LGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [LGraph.adj, or_comm]

/-- The graph on the vertices whose edges are the waved edges and the `=`-dotted edges (`7_8:172`). -/
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

/-- The probe's `mol` is the molecule of `def_poly`: the connected component of `v` in the graph of
waved and `=`-dotted edges. -/
theorem LGraph.mem_mol_iff (Γ : LGraph E I) (v w : E ⊕ I) :
    w ∈ Γ.mol v ↔ Γ.molGraph.Reachable v w := by
  constructor
  · exact Γ.reachable_of_mem_iterate _ v w
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    exact Γ.iterate_mono_nat hp.length_lt.le _ (Γ.walk_mem_iterate p)

/-- The iterates beyond `|E ⊕ I|` steps are all the molecule. -/
theorem LGraph.mem_iterate_iff (Γ : LGraph E I) {n : ℕ} (hn : Fintype.card (E ⊕ I) ≤ n)
    (v w : E ⊕ I) : w ∈ Γ.step^[n] {v} ↔ Γ.molGraph.Reachable v w :=
  ⟨Γ.reachable_of_mem_iterate n v w, fun h => by
    obtain ⟨p, hp⟩ := h.exists_isPath
    exact Γ.iterate_mono_nat (hp.length_lt.le.trans hn) _ (Γ.walk_mem_iterate p)⟩

/-! The molecules as connected components, the external and internal molecules, edges inside a
molecule and the solid edges of the molecular graph `𝒢_ℳ` (`7_8:180-187`). -/

/-- The set of molecules: the connected components of `molGraph` (`7_8:172`). -/
abbrev LGraph.Mol (Γ : LGraph E I) : Type _ := Γ.molGraph.ConnectedComponent

/-- The molecule of a vertex (`def_poly`, `7_8:172`). -/
def LGraph.molOf (Γ : LGraph E I) (v : E ⊕ I) : Γ.Mol := Γ.molGraph.connectedComponentMk v

/-- Two vertices are in the same molecule iff one is in the closure `mol` of the other. -/
theorem LGraph.molOf_eq_iff (Γ : LGraph E I) (u v : E ⊕ I) :
    Γ.molOf u = Γ.molOf v ↔ v ∈ Γ.mol u := by
  rw [Γ.mem_mol_iff]; exact SimpleGraph.ConnectedComponent.eq

/-- External molecule: it contains an external vertex (`7_8:172`). -/
def LGraph.IsExtMol (Γ : LGraph E I) (c : Γ.Mol) : Prop := ∃ a : E, Γ.molOf (Sum.inl a) = c

/-- An edge is *inside* a molecule if both of its ends belong to it (`7_8:172`). -/
def LGraph.InsideMol (Γ : LGraph E I) (u v : E ⊕ I) : Prop := Γ.molOf u = Γ.molOf v

/-- The solid edges of the molecular graph `𝒢_ℳ` (`7_8:180-187`): the vertices are the molecules,
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
(`7_8:172`, `7_8:247`). -/
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
/-! ## 6. Packed graphs and linear combinations (`ValG`, `7_8:159-164`)

The graphs of a linear combination `∑ c_i 𝒢_i` have different internal vertex sets, and a graph
obtained by merging vertices (the dotted edge partition, sections 7-10) has fewer external vertices than
the original.  A `PGraph E` is a graph `g : LGraph E' I'` together with a surjection `ext : E → E'`:
the external vertices of the original graph are read through `ext`, so that two external vertices
that were merged must carry the same label (`PGraph.val` is `0` otherwise).  The coefficient `c_i` of
the term is the field `coeff` of `g`: the record keeps `coeff : ℂ`.  No field is added to `LGraph`;
the wrapper `PGraph` is new. -/

/-- A graph whose external vertices are the image of those of `E`, with its own vertex types: a term
of a linear combination (`ValG`, `7_8:161`) or a merged graph (`dot-def`, `7_8:222`). -/
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
external vertices carry different labels (`ValG`, `7_8:159-161`). -/
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

/-- A graph is a packed graph (no merging; `ValG`, `7_8:161`). -/
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
coefficients are inside the terms; `ValG`, `7_8:161`). -/
def LComb.val (L : List (PGraph E)) (D : LData ι) (ℓe : E → ι) : ℂ :=
  (L.map fun P => P.val D ℓe).sum

end Packed

/-! ## 7. Merging the vertices joined by `=`-dotted edges (`dot-def`, `7_8:222`)

"We merge vertices connected by dotted edges."  The classes of the equivalence relation generated by
the `=`-dotted edges are the vertices of the merged graph; a class is external if it contains an
external vertex (its label is then fixed), internal otherwise.  What the paper leaves implicit
(delta candidate `T2050b`): (1) an internal vertex merged with an external one becomes external;
(2) two external vertices in one class must carry the same label (`PGraph.val`); (3) each merged
graph has its own vertex types, hence the wrapper `PGraph`; the record `LGraph` needs no new field. -/

section Merge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `u`, `v` are the two ends of a `=`-dotted edge (`dot-def`, `7_8:222`). -/
def LGraph.EqRel (Γ : LGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ e ∈ Γ.dotted, e.eq = true ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))

/-- "Connected by a path of dotted edges" (`7_8:221`): the equivalence relation generated by `EqRel`. -/
def LGraph.eqSetoid (Γ : LGraph E I) : Setoid (E ⊕ I) := Relation.EqvGen.setoid Γ.EqRel

/-- The vertices of the merged graph (`dot-def`, `7_8:222`). -/
abbrev LGraph.Cls (Γ : LGraph E I) : Type := Quotient Γ.eqSetoid

/-- The class of a vertex. -/
abbrev LGraph.cls (Γ : LGraph E I) (v : E ⊕ I) : Γ.Cls := Quotient.mk Γ.eqSetoid v

/-- A class is external if it contains an external vertex (`dot-def`, `7_8:222`; T2050b). -/
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
`1` after merging); a `×`-dotted edge inside a class makes the value `0` (`dot-def`, "inconsistent",
`7_8:221`). -/
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

/-- **Merging preserves the value** (`dot-def`, `7_8:222`), for the external labels that factor
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

/-! ## 8. Normal graphs (`defnlvl0`, `7_8:196-210`)

The predicate reads the lists `solid` and `dotted` of the record; no new field is needed. -/

section Normal

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Γ` has a solid edge between the vertices `u` and `v` (in either direction), not a loop
(`defnlvl0` (iii), `7_8:205`). -/
def LGraph.SBetween (Γ : LGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ e ∈ Γ.solid, e.src ≠ e.dst ∧ ((e.src = u ∧ e.dst = v) ∨ (e.src = v ∧ e.dst = u))

/-- `Γ` has a `×`-dotted edge `1_{x≠y}` between the vertices `u` and `v` (in either order)
(`defnlvl0` (iii), `7_8:205`). -/
def LGraph.XBetween (Γ : LGraph E I) (u v : E ⊕ I) : Prop :=
  ∃ e ∈ Γ.dotted, e.eq = false ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))

instance (Γ : LGraph E I) (u v : E ⊕ I) : Decidable (Γ.SBetween u v) := by
  unfold LGraph.SBetween; infer_instance

instance (Γ : LGraph E I) (u v : E ⊕ I) : Decidable (Γ.XBetween u v) := by
  unfold LGraph.XBetween; infer_instance

/-- **Normal graph** (`defnlvl0`, `7_8:196-210`): (ii) there are no (`=`-)dotted edges; (iii) two
different vertices are joined by a `×`-dotted edge if and only if they are joined by a solid edge;
(iv) every weight is a light-weight, i.e. every solid self-loop has a circle.  Condition (i), "at
most `O(1)` many vertices and edges", is not a property of a fixed record: it is the bound `n` that a
consumer quantifies outside (every `LGraph E I` with finite lists has finitely many).  Reading of
(iii) (delta candidate `T2050c`): `7_8:205` says "solid edge" and `dot-def` (`7_8:215`, `7_8:217`) says "`G`-edge";
here every non-loop solid edge (`G`, `Ḡ`, `G-M`, `\overline{G-M}`) counts. -/
def LGraph.Normal (Γ : LGraph E I) : Prop :=
  (∀ e ∈ Γ.dotted, e.eq = false) ∧
  (∀ u v : E ⊕ I, u ≠ v → (Γ.XBetween u v ↔ Γ.SBetween u v)) ∧
  (∀ e ∈ Γ.solid, e.src = e.dst → e.circ = true)

instance (Γ : LGraph E I) : Decidable Γ.Normal := by unfold LGraph.Normal; infer_instance

end Normal

/-! ## 9. The dotted edge partition (`dot-def`, `7_8:214-225`), first half: the expansion of the dotted edges

For each pair of vertices `{α, β}` joined by a solid edge but by no `×`-dotted edge, write
`1 = 1_{α=β} + 1_{α≠β}` (`7_8:215-216`); for each `×`-dotted edge `1_{α≠β}` with no solid edge between
`α` and `β`, write `1_{α≠β} = 1 - 1_{α=β}` (`7_8:217-218`).  Expanding the product of all these identities
gives `Γ = ∑ Dot · Γ` (`odot`), each `Dot` a product of dotted and `×`-dotted edges with a sign.  An
`atom` is the list of the terms (sign, new dotted edges) of one identity; `lwCombineAtoms` expands the
product.  The record needs no new field.  A pair `{α, β}` with several solid edges is expanded once
(`lwDedupPairs`); every `×`-dotted edge without a solid edge is expanded once (at most one dotted
edge per pair, `LGraph.DotWF`, is the paper's standing convention `7_8:141`). -/

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
`dot-def`, `7_8:215-216`). -/
def LGraph.aPairs (Γ : LGraph E I) : List ((E ⊕ I) × (E ⊕ I)) :=
  lwDedupPairs ((Γ.solid.filter fun e => decide (e.src ≠ e.dst ∧ ¬ Γ.XBetween e.src e.dst)).map
    fun e => (e.src, e.dst))

/-- The `×`-dotted edges with no solid edge between their ends (`dot-def`, `7_8:217-218`). -/
def LGraph.isB (Γ : LGraph E I) (e : DEdge (E ⊕ I)) : Bool :=
  decide (e.eq = false ∧ ¬ Γ.SBetween e.x e.y)

/-- The `×`-dotted edges to be replaced by `1 - 1_{α=β}` (`dot-def`, `7_8:217-218`). -/
def LGraph.bEdges (Γ : LGraph E I) : List (DEdge (E ⊕ I)) := Γ.dotted.filter Γ.isB

/-- The dotted edges kept unchanged (`dot-def`, `7_8:219-221`). -/
def LGraph.dotBase (Γ : LGraph E I) : List (DEdge (E ⊕ I)) := Γ.dotted.filter fun e => !Γ.isB e

/-- The identities of `dot-def` (`7_8:215-218`), as lists of terms (sign, new dotted edges). -/
def LGraph.dotAtoms (Γ : LGraph E I) : List (List (ℤ × List (DEdge (E ⊕ I)))) :=
  Γ.aPairs.map (fun p => [(1, [⟨true, p.1, p.2⟩]), (1, [⟨false, p.1, p.2⟩])]) ++
  Γ.bEdges.map (fun e => [(1, []), (-1, [⟨true, e.x, e.y⟩])])

/-- The product of a list of identities, expanded (`odot`, `7_8:219-220`). -/
def lwCombineAtoms {X : Type*} : List (List (ℤ × List X)) → List (ℤ × List X)
  | [] => [(1, [])]
  | a :: rest => a.flatMap fun o => (lwCombineAtoms rest).map fun c => (o.1 * c.1, o.2 ++ c.2)

/-- The terms `Dot` of the dotted edge partition: sign and the new dotted edges (`odot`, `7_8:221`). -/
def LGraph.dotChoices (Γ : LGraph E I) : List (ℤ × List (DEdge (E ⊕ I))) :=
  lwCombineAtoms Γ.dotAtoms

/-- The graph `Dot · Γ` of one term: the `×`-dotted edges without a solid edge are removed, the new
dotted edges are added, the sign goes into the coefficient (`dot-def`, `7_8:219-221`). -/
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

/-- `1 = 1_{α=β} + 1_{α≠β}` (`7_8:215-216`). -/
private theorem lwEvalAtom_A {V : Type*} (ℓ : V → ι) (u v : V) :
    lwEvalAtom ℓ [(1, [⟨true, u, v⟩]), (1, [⟨false, u, v⟩])] = 1 := by
  by_cases h : ℓ u = ℓ v <;> simp [lwEvalAtom, DEdge.val, h]

/-- `1_{α≠β} = 1 - 1_{α=β}` (`7_8:217-218`). -/
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

/-- **The expansion of the dotted edges** (`odot`, `7_8:219-221`) at the level of the product of the edge
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
`(G_{xx} - m)` plus a coefficient `m` (resp. `\overline{(G_{xx} - m)}` plus `\bar m`)" (`7_8:222`).
Here `M = m I` (`1_2:344`): the split needs `M_{xx} = m`, a hypothesis `∀ x, D.M x x = m` of the value
identities (`M` is a general matrix in `LData`).  `m` is a parameter of the partition: the coefficients
"polynomial in `m, m̄, …`" (`7_8:144`) are plain complex numbers in the record (delta candidate
`T2050a`). -/

section Weights

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Split every weight (a self-loop without circle) of a list of solid edges into a light-weight and
a coefficient; the result is the list of terms (coefficient, edges) (`dot-def`, `7_8:222`). -/
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
`m̄` (`dot-def`, `7_8:222`). -/
def LGraph.splitWeights (m : ℂ) (Δ : LGraph E I) : List (LGraph E I) :=
  (lwSplitLoops m Δ.solid).map fun r => { Δ with solid := r.2, coeff := r.1 * Δ.coeff }

/-- **The weight split preserves the value** (`dot-def`, `7_8:222`): `G_{xx} = (G_{xx} - m) + m` and `Ḡ_{xx} = \overline{(G_{xx} - m)} + \bar m` for `M_{xx} = m`. -/
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
dotted edges (`dot-def`, `7_8:221`): then `Dot · Γ = 0`. -/
def LGraph.Consistent (Γ : LGraph E I) : Prop :=
  ∀ e ∈ Γ.dotted, e.eq = false → ¬ Γ.cls e.x = Γ.cls e.y

/-- An inconsistent term `Dot · Γ` (a `×`-dotted edge inside a class of `=`-dotted edges) has product `0` at every labelling (`7_8:221`). -/
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

/-- The merged graph of a term, with its weights split: a list of packed graphs (`dot-def`, `7_8:222`). -/
def LGraph.mergeSplitP (m : ℂ) (Δ : LGraph E I) : List (PGraph E) :=
  (Δ.merge.splitWeights m).map fun g =>
    { E' := Δ.ExtCls, I' := Δ.IntCls, ext := Δ.extMap, ext_surj := Δ.extMap_surj, g := g }

/-- The terms `Dot · Γ` of the dotted edge partition that are consistent (`dot-def`, `7_8:221`). -/
def LGraph.partitionTerms (Γ : LGraph E I) : List (LGraph E I) :=
  open Classical in
  (Γ.dotChoices.map Γ.withDots).filter fun Δ => decide Δ.Consistent

/-- **The dotted edge partition** (`dot-def`, `7_8:214-225`): the linear combination of normal graphs
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

/-- **The dotted edge partition preserves the value** (`dot-def`, `7_8:221-222`): the value of `Γ` is
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

/-- **The terms of the partition are normal graphs** (`dot-def`, `7_8:222`): every term of the
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

/-! ## 12. Scaling size and scaling order (`def scaling`, `7_8:232-255`; `def scaling order`, `7_8:270-284`)

The scaling size and order of a **normal** graph are functions of its counters (`LGraph.counters`,
the merged `RBM.Graph.Counters`).  For a general graph the paper defines them through the dotted edge
partition: `size = max_k size(Γ_k)` and `ord = min_k ord(Γ_k)` over the normal graphs `Γ_k` of
`LGraph.partition` (`7_8:248-250`, `7_8:282-283`).  When the partition is empty (all terms inconsistent:
the graph is `0`) the maximum is `0` and the minimum is `⊤` (delta candidate `T2050b`).  `Ψ_t` is a
parameter `Ψ`; `W`, `d`, `L` are the model parameters.  The record needs no new field: the counters
`LGraph.counters` of the probe are all that `size` and `ord` read. -/

section Scaling

/-- `(eq_defsize)` (`7_8:238-241`): `size(Γ) = (L^d)^{n_M} Ψ^{n_S} W^{-d (n_W - n_V)}`, an integer power
of `W`. -/
def Counters.scalingSize (c : Counters) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  ((L : ℝ) ^ d) ^ c.nM * Ψ ^ c.nS * (W : ℝ) ^ (-(d : ℤ) * ((c.nW : ℤ) - (c.nV : ℤ)))

/-- The identity of `7_8:274-275`: `size(Γ) = (L^d)^{n_M} Ψ^{ord(Γ)} (W^d Ψ²)^{n_V - n_W}`. -/
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

/-- `7_8:276-277`: `size(Γ) ≤ (L^d)^{n_M} Ψ^{ord(Γ)}` whenever `n_W ≥ n_V`, given `Ψ ≥ W^{-d/2}`
(in the form `1 ≤ W^d Ψ²`, see `one_le_pow_mul_sq_iff`). -/
theorem Counters.scalingSize_le (c : Counters) {Ψ : ℝ} (W d L : ℕ) (hΨ : 0 < Ψ)
    (hWΨ : 1 ≤ (W : ℝ) ^ d * Ψ ^ 2) (h : c.nV ≤ c.nW) :
    c.scalingSize Ψ W d L ≤ ((L : ℝ) ^ d) ^ c.nM * Ψ ^ (ord c) := by
  rw [c.scalingSize_eq W d L hΨ.ne']
  have hle : ((W : ℝ) ^ d * Ψ ^ 2) ^ ((c.nV : ℤ) - c.nW) ≤ 1 := zpow_le_one_of_nonpos₀ hWΨ (by omega)
  have hnn : 0 ≤ ((L : ℝ) ^ d) ^ c.nM * Ψ ^ (ord c) :=
    mul_nonneg (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _) (zpow_nonneg hΨ.le _)
  calc _ ≤ ((L : ℝ) ^ d) ^ c.nM * Ψ ^ (ord c) * 1 := mul_le_mul_of_nonneg_left hle hnn
    _ = _ := mul_one _

/-- The window `Ψ ≥ W^{-d/2}` (`7_8:276`) is `W^d Ψ² ≥ 1`. -/
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

/-- The scaling size of a normal graph (`def scaling`, `7_8:232-241`). -/
def LGraph.scalingSize (Γ : LGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  Γ.counters.scalingSize Ψ W d L

/-- The scaling order of a normal graph (`def scaling order`, `7_8:270-272`), `(eq:ordG)`: the
merged `RBM.Graph.ord` of the counters. -/
def LGraph.scalingOrder (Γ : LGraph E I) : ℤ := ord Γ.counters

/-- The scaling size of a general graph (`7_8:248-250`): the maximum of the sizes of the normal graphs
of the dotted edge partition (`0` for the empty partition). -/
def LGraph.scalingSizeG (m : ℂ) (Γ : LGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  ((Γ.partition m).map fun P => P.g.scalingSize Ψ W d L).foldr max 0

/-- The scaling order of a general graph (`7_8:282-283`): the minimum of the orders of the normal graphs
of the dotted edge partition (`⊤` for the empty partition). -/
def LGraph.scalingOrderG (m : ℂ) (Γ : LGraph E I) : WithTop ℤ :=
  ((Γ.partition m).map fun P => ((P.g.scalingOrder : ℤ) : WithTop ℤ)).foldr min ⊤

/-- `k ≤ ord(Γ)` for a general graph iff `k ≤ ord(Γ_k)` for every normal graph `Γ_k` of the partition (the minimum `7_8:282-283`). -/
theorem LGraph.le_scalingOrderG_iff (m : ℂ) (Γ : LGraph E I) (k : ℤ) :
    ((k : ℤ) : WithTop ℤ) ≤ Γ.scalingOrderG m ↔ ∀ P ∈ Γ.partition m, k ≤ P.g.scalingOrder := by
  unfold LGraph.scalingOrderG
  generalize Γ.partition m = L
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.map_cons, List.foldr_cons, le_min_iff, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    simp [WithTop.coe_le_coe]

/-- `size(Γ) ≤ B` for a general graph iff `0 ≤ B` and `size(Γ_k) ≤ B` for every normal graph `Γ_k` of the partition (the maximum `7_8:248-249`). -/
theorem LGraph.scalingSizeG_le_iff (m : ℂ) (Γ : LGraph E I) (Ψ : ℝ) (W d L : ℕ) (B : ℝ) :
    Γ.scalingSizeG m Ψ W d L ≤ B ↔
      0 ≤ B ∧ ∀ P ∈ Γ.partition m, P.g.scalingSize Ψ W d L ≤ B := by
  unfold LGraph.scalingSizeG
  generalize Γ.partition m = L'
  induction L' with
  | nil => simp
  | cons P L' ih =>
    simp only [List.map_cons, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    tauto

end Graphs

end Scaling

/-! ## 13. Basic lemmas: no internal vertices, relabeling, disjoint unions -/

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The value of a graph with no internal vertices** is the product of the edge factors and the
coefficient at the external labels: the sum over `I → ι` has one term. -/
theorem LGraph.val_of_isEmpty {E I : Type*} [Fintype I] [DecidableEq I] [IsEmpty I]
    (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) (ℓi : I → ι) :
    Γ.val D ℓe = Γ.term D (Sum.elim ℓe ℓi) := by
  unfold LGraph.val
  have : Unique (I → ι) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique]
  congr 1
  exact congrArg _ (Subsingleton.elim _ _)

/-- The value of a graph with `n_V = 0`, unfolded. -/
theorem LGraph.val_of_isEmpty_prod {E I : Type*} [Fintype I] [DecidableEq I] [IsEmpty I]
    (Γ : LGraph E I) (D : LData ι) (ℓe : E → ι) (ℓi : I → ι) :
    Γ.val D ℓe = Γ.coeff * (Γ.solid.map (SEdge.val D (Sum.elim ℓe ℓi))).prod *
      (Γ.waved.map (WEdge.val D (Sum.elim ℓe ℓi))).prod *
      (Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod := by
  rw [Γ.val_of_isEmpty D ℓe ℓi]
  rfl

/-- **Value under relabeling the vertices** by bijections of the external and of the internal vertex
sets: the internal sum is reindexed. -/
theorem LGraph.val_relabel_equiv {E E' I I' : Type*} [Fintype I] [DecidableEq I] [Fintype I']
    [DecidableEq I'] (Γ : LGraph E I) (eE : E ≃ E') (eI : I ≃ I') (D : LData ι) (ℓe' : E' → ι) :
    (Γ.relabel (Equiv.sumCongr eE eI)).val D ℓe' = Γ.val D (ℓe' ∘ eE) := by
  unfold LGraph.val
  refine Fintype.sum_equiv (Equiv.arrowCongr eI.symm (Equiv.refl ι)) _ _ fun ℓi' => ?_
  rw [LGraph.term_relabel]
  congr 1
  funext v
  rcases v with a | b <;> simp [Equiv.arrowCongr]

/-- Relabeling the labels `ι ≃ ι'` (a bijection of the lattice carrying the matrices along). -/
def LData.map {ι ι' : Type*} (σ : ι ≃ ι') (D : LData ι) : LData ι' where
  G := fun a b => D.G (σ.symm a) (σ.symm b)
  M := fun a b => D.M (σ.symm a) (σ.symm b)
  S := fun a b => D.S (σ.symm a) (σ.symm b)
  Sp := fun a b => D.Sp (σ.symm a) (σ.symm b)

private theorem LGraph.term_map {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {E I : Type*} (Γ : LGraph E I) (σ : ι ≃ ι') (D : LData ι)
    (ℓ : E ⊕ I → ι') : Γ.term (D.map σ) ℓ = Γ.term D (σ.symm ∘ ℓ) := by
  have hS : SEdge.val (D.map σ) ℓ = SEdge.val D (σ.symm ∘ ℓ) := rfl
  have hW : WEdge.val (D.map σ) ℓ = WEdge.val D (σ.symm ∘ ℓ) := rfl
  have hD : DEdge.val ℓ = DEdge.val (σ.symm ∘ ℓ) := by
    funext e
    simp [DEdge.val]
  simp only [LGraph.term, hS, hW, hD]

/-- **Value under relabeling the labels**: carrying the matrices and the external labels along a
bijection `σ : ι ≃ ι'` of the lattice leaves the value unchanged. -/
theorem LGraph.val_map_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {E I : Type*} [Fintype I]
    [DecidableEq I] (Γ : LGraph E I) (σ : ι ≃ ι') (D : LData ι) (ℓe : E → ι) :
    Γ.val (D.map σ) (σ ∘ ℓe) = Γ.val D ℓe := by
  unfold LGraph.val
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl I) σ).symm _ _ fun ℓi' => ?_
  rw [Γ.term_map]
  congr 1
  funext v
  rcases v with a | b <;> simp [Equiv.arrowCongr]

end Basic

/-! ## 14. Disjoint unions

The disjoint union of two graphs (no edge between the parts, the coefficients multiplied) has the
product of the two values, and every counter is additive. -/

section Union

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
  [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]

/-- The vertices of the first part in the union. -/
def lwUnionV₁ : E₁ ⊕ I₁ → (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂) := Sum.map Sum.inl Sum.inl

/-- The vertices of the second part in the union. -/
def lwUnionV₂ : E₂ ⊕ I₂ → (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂) := Sum.map Sum.inr Sum.inr

private theorem lwUnionV₁_injective : Function.Injective (lwUnionV₁ (E₁ := E₁) (I₁ := I₁) (E₂ := E₂) (I₂ := I₂)) :=
  Sum.map_injective.2 ⟨Sum.inl_injective, Sum.inl_injective⟩

private theorem lwUnionV₂_injective : Function.Injective (lwUnionV₂ (E₁ := E₁) (I₁ := I₁) (E₂ := E₂) (I₂ := I₂)) :=
  Sum.map_injective.2 ⟨Sum.inr_injective, Sum.inr_injective⟩

/-- The disjoint union of two graphs: the edges of both, no edge between them, the product of the
coefficients. -/
def LGraph.disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) : LGraph (E₁ ⊕ E₂) (I₁ ⊕ I₂) where
  solid := Γ₁.solid.map (SEdge.map lwUnionV₁) ++ Γ₂.solid.map (SEdge.map lwUnionV₂)
  waved := Γ₁.waved.map (WEdge.map lwUnionV₁) ++ Γ₂.waved.map (WEdge.map lwUnionV₂)
  dotted := Γ₁.dotted.map (DEdge.map lwUnionV₁) ++ Γ₂.dotted.map (DEdge.map lwUnionV₂)
  coeff := Γ₁.coeff * Γ₂.coeff

private theorem LGraph.term_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (D : LData ι)
    (ℓ : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂) → ι) :
    (Γ₁.disjUnion Γ₂).term D ℓ = Γ₁.term D (ℓ ∘ lwUnionV₁) * Γ₂.term D (ℓ ∘ lwUnionV₂) := by
  have hS₁ : (SEdge.val D ℓ) ∘ (SEdge.map lwUnionV₁) = SEdge.val D (ℓ ∘ lwUnionV₁) := funext fun e => rfl
  have hS₂ : (SEdge.val D ℓ) ∘ (SEdge.map lwUnionV₂) = SEdge.val D (ℓ ∘ lwUnionV₂) := funext fun e => rfl
  have hW₁ : (WEdge.val D ℓ) ∘ (WEdge.map lwUnionV₁) = WEdge.val D (ℓ ∘ lwUnionV₁) := funext fun e => rfl
  have hW₂ : (WEdge.val D ℓ) ∘ (WEdge.map lwUnionV₂) = WEdge.val D (ℓ ∘ lwUnionV₂) := funext fun e => rfl
  have hD₁ : (DEdge.val ℓ) ∘ (DEdge.map lwUnionV₁) = DEdge.val (ℓ ∘ lwUnionV₁) := funext fun e => rfl
  have hD₂ : (DEdge.val ℓ) ∘ (DEdge.map lwUnionV₂) = DEdge.val (ℓ ∘ lwUnionV₂) := funext fun e => rfl
  simp only [LGraph.term, LGraph.disjUnion, List.map_append, List.prod_append, List.map_map, hS₁,
    hS₂, hW₁, hW₂, hD₁, hD₂]
  ring

/-- **The value of a disjoint union is the product of the values**. -/
theorem LGraph.val_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (D : LData ι)
    (ℓ₁ : E₁ → ι) (ℓ₂ : E₂ → ι) :
    (Γ₁.disjUnion Γ₂).val D (Sum.elim ℓ₁ ℓ₂) = Γ₁.val D ℓ₁ * Γ₂.val D ℓ₂ := by
  unfold LGraph.val
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I₁ I₂ ι) _ _ fun ℓi => ?_
  rw [LGraph.term_disjUnion]
  congr 2
  · funext v
    rcases v with a | b <;> simp [lwUnionV₁, Equiv.sumArrowEquivProdArrow]
  · funext v
    rcases v with a | b <;> simp [lwUnionV₂, Equiv.sumArrowEquivProdArrow]

/-- `n_S` is additive under disjoint union. -/
theorem LGraph.nS_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) :
    (Γ₁.disjUnion Γ₂).nS = Γ₁.nS + Γ₂.nS := by
  simp [LGraph.nS, LGraph.disjUnion]

/-- `n_W` is additive under disjoint union. -/
theorem LGraph.nW_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) :
    (Γ₁.disjUnion Γ₂).nW = Γ₁.nW + Γ₂.nW := by
  simp [LGraph.nW, LGraph.disjUnion]

/-- `n_V` is additive under disjoint union. -/
theorem LGraph.nV_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) :
    (Γ₁.disjUnion Γ₂).nV = Γ₁.nV + Γ₂.nV := by
  simp [LGraph.nV, Fintype.card_sum]

private theorem lwUnionV_cases (w : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) :
    (∃ u, w = lwUnionV₁ u) ∨ (∃ u, w = lwUnionV₂ u) := by
  rcases w with (a | a) | (b | b)
  · exact Or.inl ⟨Sum.inl a, rfl⟩
  · exact Or.inr ⟨Sum.inl a, rfl⟩
  · exact Or.inl ⟨Sum.inr b, rfl⟩
  · exact Or.inr ⟨Sum.inr b, rfl⟩

private theorem lwUnionV₁_ne_unionV₂ (u : E₁ ⊕ I₁) (v : E₂ ⊕ I₂) :
    (lwUnionV₁ u : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) ≠ lwUnionV₂ v := by
  rcases u with a | a <;> rcases v with b | b <;> simp [lwUnionV₁, lwUnionV₂]

private theorem LGraph.adj_iff {E I : Type*} (Γ : LGraph E I) [DecidableEq E] [DecidableEq I] (u v : E ⊕ I) :
    Γ.adj u v = true ↔
      (∃ e ∈ Γ.waved, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) ∨
      (∃ e ∈ Γ.dotted, e.eq = true ∧ ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) := by
  simp [LGraph.adj, List.any_eq_true]

private theorem lwUnionV₁_eq_unionV₂ (u : E₁ ⊕ I₁) (v : E₂ ⊕ I₂) :
    (lwUnionV₁ u : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) = lwUnionV₂ v ↔ False :=
  iff_false_intro (lwUnionV₁_ne_unionV₂ u v)

private theorem lwUnionV₂_eq_unionV₁ (u : E₁ ⊕ I₁) (v : E₂ ⊕ I₂) :
    (lwUnionV₂ v : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) = lwUnionV₁ u ↔ False :=
  iff_false_intro (lwUnionV₁_ne_unionV₂ u v).symm

private theorem lwUnionV₁_eq_iff (u v : E₁ ⊕ I₁) :
    (lwUnionV₁ u : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) = lwUnionV₁ v ↔ u = v := lwUnionV₁_injective.eq_iff

private theorem lwUnionV₂_eq_iff (u v : E₂ ⊕ I₂) :
    (lwUnionV₂ u : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) = lwUnionV₂ v ↔ u = v := lwUnionV₂_injective.eq_iff

private theorem lwAdj_union₁ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (u v : E₁ ⊕ I₁) :
    (Γ₁.disjUnion Γ₂).adj (lwUnionV₁ u) (lwUnionV₁ v) = Γ₁.adj u v := by
  rw [Bool.eq_iff_iff, LGraph.adj_iff, LGraph.adj_iff]
  simp [LGraph.disjUnion, WEdge.map, DEdge.map, lwUnionV₁_eq_iff, lwUnionV₂_eq_unionV₁,
    or_and_right, exists_or]

private theorem lwAdj_union₂ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (u v : E₂ ⊕ I₂) :
    (Γ₁.disjUnion Γ₂).adj (lwUnionV₂ u) (lwUnionV₂ v) = Γ₂.adj u v := by
  rw [Bool.eq_iff_iff, LGraph.adj_iff, LGraph.adj_iff]
  simp [LGraph.disjUnion, WEdge.map, DEdge.map, lwUnionV₂_eq_iff, lwUnionV₁_eq_unionV₂,
    or_and_right, exists_or]

private theorem lwAdj_union₁₂ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (u : E₁ ⊕ I₁) (v : E₂ ⊕ I₂) :
    (Γ₁.disjUnion Γ₂).adj (lwUnionV₁ u) (lwUnionV₂ v) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [LGraph.adj_iff] at h
  simp [LGraph.disjUnion, WEdge.map, DEdge.map, lwUnionV₁_eq_iff, lwUnionV₂_eq_iff, lwUnionV₁_eq_unionV₂,
    lwUnionV₂_eq_unionV₁, or_and_right, exists_or] at h

private theorem lwAdj_union₂₁ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (u : E₁ ⊕ I₁) (v : E₂ ⊕ I₂) :
    (Γ₁.disjUnion Γ₂).adj (lwUnionV₂ v) (lwUnionV₁ u) = false := by
  rw [LGraph.adj_comm]
  exact lwAdj_union₁₂ Γ₁ Γ₂ u v

private theorem lwStep_union₁ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (s : Finset (E₁ ⊕ I₁)) :
    (Γ₁.disjUnion Γ₂).step (s.image lwUnionV₁) = (Γ₁.step s).image lwUnionV₁ := by
  ext w
  simp only [LGraph.step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  rcases lwUnionV_cases w with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · constructor
    · rintro (⟨x, hx, hxu⟩ | ⟨v, ⟨x, hx, rfl⟩, hadj⟩)
      · exact ⟨x, Or.inl hx, hxu⟩
      · rw [lwAdj_union₁] at hadj
        exact ⟨u, Or.inr ⟨x, hx, hadj⟩, rfl⟩
    · rintro ⟨x, hx | ⟨v, hv, hadj⟩, hxu⟩
      · exact Or.inl ⟨x, hx, hxu⟩
      · obtain rfl := lwUnionV₁_injective hxu
        exact Or.inr ⟨lwUnionV₁ v, ⟨v, hv, rfl⟩, by rw [lwAdj_union₁]; exact hadj⟩
  · constructor
    · rintro (⟨x, _, hx⟩ | ⟨v, ⟨x, _, rfl⟩, hadj⟩)
      · exact absurd hx (lwUnionV₁_ne_unionV₂ _ _)
      · rw [lwAdj_union₁₂] at hadj
        exact absurd hadj (by simp)
    · rintro ⟨x, _, hx⟩
      exact absurd hx (lwUnionV₁_ne_unionV₂ _ _)

private theorem lwStep_union₂ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (s : Finset (E₂ ⊕ I₂)) :
    (Γ₁.disjUnion Γ₂).step (s.image lwUnionV₂) = (Γ₂.step s).image lwUnionV₂ := by
  ext w
  simp only [LGraph.step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  rcases lwUnionV_cases w with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · constructor
    · rintro (⟨x, _, hx⟩ | ⟨v, ⟨x, _, rfl⟩, hadj⟩)
      · exact absurd hx.symm (lwUnionV₁_ne_unionV₂ _ _)
      · rw [lwAdj_union₂₁] at hadj
        exact absurd hadj (by simp)
    · rintro ⟨x, _, hx⟩
      exact absurd hx.symm (lwUnionV₁_ne_unionV₂ _ _)
  · constructor
    · rintro (⟨x, hx, hxu⟩ | ⟨v, ⟨x, hx, rfl⟩, hadj⟩)
      · exact ⟨x, Or.inl hx, hxu⟩
      · rw [lwAdj_union₂] at hadj
        exact ⟨u, Or.inr ⟨x, hx, hadj⟩, rfl⟩
    · rintro ⟨x, hx | ⟨v, hv, hadj⟩, hxu⟩
      · exact Or.inl ⟨x, hx, hxu⟩
      · obtain rfl := lwUnionV₂_injective hxu
        exact Or.inr ⟨lwUnionV₂ v, ⟨v, hv, rfl⟩, by rw [lwAdj_union₂]; exact hadj⟩

private theorem lwIterate_union₁ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (n : ℕ) :
    ∀ s : Finset (E₁ ⊕ I₁), (Γ₁.disjUnion Γ₂).step^[n] (s.image lwUnionV₁) =
      (Γ₁.step^[n] s).image lwUnionV₁ := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, lwStep_union₁, ih]

private theorem lwIterate_union₂ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (n : ℕ) :
    ∀ s : Finset (E₂ ⊕ I₂), (Γ₁.disjUnion Γ₂).step^[n] (s.image lwUnionV₂) =
      (Γ₂.step^[n] s).image lwUnionV₂ := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, lwStep_union₂, ih]

private theorem lwMol_union₁ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (u : E₁ ⊕ I₁) :
    (Γ₁.disjUnion Γ₂).mol (lwUnionV₁ u) = (Γ₁.mol u).image lwUnionV₁ := by
  unfold LGraph.mol
  rw [← Finset.image_singleton, lwIterate_union₁]
  congr 1
  ext w
  rw [Γ₁.mem_iterate_iff (Fintype.card_le_of_injective _ lwUnionV₁_injective),
    Γ₁.mem_iterate_iff le_rfl]

private theorem lwMol_union₂ (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) (u : E₂ ⊕ I₂) :
    (Γ₁.disjUnion Γ₂).mol (lwUnionV₂ u) = (Γ₂.mol u).image lwUnionV₂ := by
  unfold LGraph.mol
  rw [← Finset.image_singleton, lwIterate_union₂]
  congr 1
  ext w
  rw [Γ₂.mem_iterate_iff (Fintype.card_le_of_injective _ lwUnionV₂_injective),
    Γ₂.mem_iterate_iff le_rfl]

private theorem lwIsRight_unionV₁ (w : E₁ ⊕ I₁) :
    (lwUnionV₁ w : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)).isRight = w.isRight := by
  rcases w with a | a <;> rfl

private theorem lwIsRight_unionV₂ (w : E₂ ⊕ I₂) :
    (lwUnionV₂ w : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)).isRight = w.isRight := by
  rcases w with a | a <;> rfl

private theorem lwSelf_mem_mol {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (u : E ⊕ I) : u ∈ Γ.mol u :=
  (Γ.mem_mol_iff u u).2 (SimpleGraph.Reachable.refl u)

/-- **The counter `n_M` is additive under disjoint union**: the molecules of the union are those of
the two parts. -/
theorem LGraph.nM_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) :
    (Γ₁.disjUnion Γ₂).nM = Γ₁.nM + Γ₂.nM := by
  classical
  unfold LGraph.nM
  set A₁ := (Finset.univ.filter fun v : E₁ ⊕ I₁ => ∀ w ∈ Γ₁.mol v, w.isRight = true).image Γ₁.mol
  set A₂ := (Finset.univ.filter fun v : E₂ ⊕ I₂ => ∀ w ∈ Γ₂.mol v, w.isRight = true).image Γ₂.mol
  have hset : (Finset.univ.filter fun v => ∀ w ∈ (Γ₁.disjUnion Γ₂).mol v, w.isRight = true).image
      (Γ₁.disjUnion Γ₂).mol = A₁.image (Finset.image lwUnionV₁) ∪ A₂.image (Finset.image lwUnionV₂) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, A₁, A₂]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases lwUnionV_cases v with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · left
        refine ⟨Γ₁.mol u, ⟨u, ?_, rfl⟩, (lwMol_union₁ Γ₁ Γ₂ u).symm⟩
        intro w hw
        have := hv (lwUnionV₁ w) (by rw [lwMol_union₁]; exact Finset.mem_image_of_mem _ hw)
        rwa [lwIsRight_unionV₁] at this
      · right
        refine ⟨Γ₂.mol u, ⟨u, ?_, rfl⟩, (lwMol_union₂ Γ₁ Γ₂ u).symm⟩
        intro w hw
        have := hv (lwUnionV₂ w) (by rw [lwMol_union₂]; exact Finset.mem_image_of_mem _ hw)
        rwa [lwIsRight_unionV₂] at this
    · rintro (⟨_, ⟨u, hu, rfl⟩, rfl⟩ | ⟨_, ⟨u, hu, rfl⟩, rfl⟩)
      · refine ⟨lwUnionV₁ u, ?_, lwMol_union₁ Γ₁ Γ₂ u⟩
        intro w hw
        rw [lwMol_union₁] at hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
        rw [lwIsRight_unionV₁]
        exact hu x hx
      · refine ⟨lwUnionV₂ u, ?_, lwMol_union₂ Γ₁ Γ₂ u⟩
        intro w hw
        rw [lwMol_union₂] at hw
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
        rw [lwIsRight_unionV₂]
        exact hu x hx
  rw [hset, Finset.card_union_of_disjoint, Finset.card_image_of_injective _
      (Finset.image_injective lwUnionV₁_injective), Finset.card_image_of_injective _
      (Finset.image_injective lwUnionV₂_injective)]
  rw [Finset.disjoint_left]
  intro T h1 h2
  obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨T₂, hT₂, h⟩ := Finset.mem_image.1 h2
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hT₁
  have hu : (lwUnionV₁ u : (E₁ ⊕ E₂) ⊕ (I₁ ⊕ I₂)) ∈
      Finset.image (lwUnionV₁ (E₂ := E₂) (I₂ := I₂)) (Γ₁.mol u) :=
    Finset.mem_image_of_mem _ (lwSelf_mem_mol Γ₁ u)
  rw [← h] at hu
  obtain ⟨x, _, hx⟩ := Finset.mem_image.1 hu
  exact lwUnionV₁_ne_unionV₂ u x hx.symm

/-- **Counters are additive under disjoint union** (the four counters of `Counters`; `nlw`, `ndv` are
`0`), hence so is `ord`. -/
theorem LGraph.ord_disjUnion (Γ₁ : LGraph E₁ I₁) (Γ₂ : LGraph E₂ I₂) :
    ord (Γ₁.disjUnion Γ₂).counters = ord Γ₁.counters + ord Γ₂.counters := by
  simp only [LGraph.counters, ord, LGraph.nS_disjUnion, LGraph.nW_disjUnion, LGraph.nV_disjUnion]
  push_cast
  ring

end Union

/-! ## 14b. Counters are invariant under a bijective relabeling -/

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

/-! ## 14c. The partition of a normal graph is the graph itself

For a normal graph with well-formed dotted edges the dotted edge partition has one term, the graph
itself (up to the isomorphism of merging singleton classes), so that the general scaling order and
size agree with those of `def scaling` and `def scaling order` of a normal graph. -/

section NormalAgree

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem lwNormal_aPairs (Γ : LGraph E I) (hN : Γ.Normal) : Γ.aPairs = [] := by
  unfold LGraph.aPairs
  have : (Γ.solid.filter fun e => decide (e.src ≠ e.dst ∧ ¬ Γ.XBetween e.src e.dst)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [decide_eq_true_eq, not_and, not_not]
    intro hne
    exact (hN.2.1 _ _ hne).2 ⟨e, he, hne, Or.inl ⟨rfl, rfl⟩⟩
  rw [this]
  rfl

private theorem lwNormal_bEdges (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    Γ.bEdges = [] := by
  unfold LGraph.bEdges
  rw [List.filter_eq_nil_iff]
  intro e he
  simp only [LGraph.isB, decide_eq_true_eq, not_and, not_not]
  intro heq
  exact (hN.2.1 _ _ (hW.2 e he)).1 ⟨e, he, heq, Or.inl ⟨rfl, rfl⟩⟩

private theorem lwNormal_dotChoices (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    Γ.dotChoices = [(1, [])] := by
  simp [LGraph.dotChoices, LGraph.dotAtoms, lwNormal_aPairs Γ hN, lwNormal_bEdges Γ hN hW,
    lwCombineAtoms]

private theorem lwNormal_dotBase (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    Γ.dotBase = Γ.dotted := by
  unfold LGraph.dotBase
  rw [List.filter_eq_self]
  intro e he
  have : Γ.isB e = false := by
    by_contra h
    have h' : Γ.isB e = true := by simpa using h
    have := List.mem_filter.2 (⟨he, h'⟩ : e ∈ Γ.dotted ∧ Γ.isB e = true)
    rw [show Γ.dotted.filter Γ.isB = Γ.bEdges from rfl, lwNormal_bEdges Γ hN hW] at this
    simp at this
  simp [this]

private theorem lwNormal_withDots (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    Γ.withDots (1, []) = Γ := by
  cases Γ
  simp only [LGraph.withDots, List.append_nil, Int.cast_one, one_mul]
  rw [lwNormal_dotBase _ hN hW]

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

private theorem lwNormal_consistent (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    Γ.Consistent := fun e he _ hcls => hW.2 e he ((lwCls_eq_iff Γ hN.1 _ _).1 hcls)

private theorem lwVmapC_injective (Γ : LGraph E I) : Function.Injective Γ.vmapC := by
  intro q q' h
  unfold LGraph.vmapC at h
  by_cases hq : Γ.IsExtCls q <;> by_cases hq' : Γ.IsExtCls q' <;> simp [hq, hq'] at h
  · exact h
  · exact h

private theorem lwVmap_injective (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    Function.Injective Γ.vmap := by
  intro u v huv
  exact (lwCls_eq_iff Γ h u v).1 (lwVmapC_injective Γ huv)

private theorem lwVmap_surjective (Γ : LGraph E I) : Function.Surjective Γ.vmap := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [LGraph.vmap, LGraph.vmapC, hq]⟩

private theorem lwVmap_isRight (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (v : E ⊕ I) :
    (Γ.vmap v).isRight = v.isRight := by
  rcases v with a | b
  · rw [LGraph.vmap_inl]; rfl
  · have hq : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b)) := by
      rintro ⟨a, ha⟩
      exact absurd ((lwCls_eq_iff Γ h _ _).1 ha) (by simp)
    rw [LGraph.vmap_inr_int Γ b hq]
    rfl

private theorem lwSplitLoops_of_circ (m : ℂ) {V : Type*} [DecidableEq V] :
    ∀ es : List (SEdge V), (∀ e ∈ es, e.src = e.dst → e.circ = true) →
      lwSplitLoops m es = [(1, es)]
  | [], _ => rfl
  | e :: es, h => by
    have ih := lwSplitLoops_of_circ m es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have hc : ¬ (e.src = e.dst ∧ e.circ = false) := fun ⟨h1, h2⟩ => by
      have := h e List.mem_cons_self h1
      rw [h2] at this
      exact absurd this (by simp)
    simp [lwSplitLoops, ih, hc]

/-- **The dotted edge partition of a normal graph is the graph**: one term, a graph isomorphic to
`Γ` (the singleton classes of the vertices), with the counters of `Γ`. -/
theorem LGraph.partition_of_normal (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    ∃ P : PGraph E, Γ.partition m = [P] ∧ P.g.nS = Γ.nS ∧ P.g.nW = Γ.nW ∧ P.g.nV = Γ.nV ∧
      P.g.nM = Γ.nM := by
  classical
  set φ : E ⊕ I ≃ Γ.ExtCls ⊕ Γ.IntCls :=
    Equiv.ofBijective Γ.vmap ⟨lwVmap_injective Γ hN.1, lwVmap_surjective Γ⟩ with hφ
  have hrel : Γ.merge = Γ.relabel φ := by
    have hd : (Γ.dotted.filter fun e => !e.eq) = Γ.dotted := by
      rw [List.filter_eq_self]
      intro e he
      simp [hN.1 e he]
    unfold LGraph.merge LGraph.relabel
    simp only [hφ, hd]
    rfl
  have hsplit : Γ.merge.splitWeights m = [Γ.merge] := by
    have hc : ∀ e ∈ Γ.merge.solid, e.src = e.dst → e.circ = true := by
      intro e' he' hloop
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      have hloop' : Γ.vmap e.src = Γ.vmap e.dst := hloop
      exact hN.2.2 e he (lwVmap_injective Γ hN.1 hloop')
    simp [LGraph.splitWeights, lwSplitLoops_of_circ m _ hc]
  let P : PGraph E :=
    { E' := Γ.ExtCls, I' := Γ.IntCls, ext := Γ.extMap, ext_surj := Γ.extMap_surj,
      g := Γ.merge }
  refine ⟨P, ?_, ?_⟩
  · unfold LGraph.partition LGraph.partitionTerms
    rw [lwNormal_dotChoices Γ hN hW]
    simp only [List.map_cons, List.map_nil, lwNormal_withDots Γ hN hW]
    have hcons : decide Γ.Consistent = true := by
      classical
      exact decide_eq_true (lwNormal_consistent Γ hN hW)
    simp [hcons, LGraph.mergeSplitP, hsplit]
    rfl
  · have h := Γ.counters_relabel_equiv φ (lwVmap_isRight Γ hN.1)
    rw [← hrel] at h
    exact h

/-- On a normal graph the scaling order of a general graph is the scaling order. -/
theorem LGraph.scalingOrderG_of_normal (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF) :
    Γ.scalingOrderG m = ((Γ.scalingOrder : ℤ) : WithTop ℤ) := by
  obtain ⟨P, hP, h1, h2, h3, h4⟩ := Γ.partition_of_normal m hN hW
  have hc : P.g.counters = Γ.counters := by
    simp only [LGraph.counters, h1, h2, h3, h4]
  simp [LGraph.scalingOrderG, hP, LGraph.scalingOrder, hc]

/-- On a normal graph the scaling size of a general graph is the scaling size (`Ψ ≥ 0`). -/
theorem LGraph.scalingSizeG_of_normal (m : ℂ) (Γ : LGraph E I) (hN : Γ.Normal) (hW : Γ.DotWF)
    {Ψ : ℝ} (hΨ : 0 ≤ Ψ) (W d L : ℕ) :
    Γ.scalingSizeG m Ψ W d L = Γ.scalingSize Ψ W d L := by
  obtain ⟨P, hP, h1, h2, h3, h4⟩ := Γ.partition_of_normal m hN hW
  have hc : P.g.counters = Γ.counters := by
    simp only [LGraph.counters, h1, h2, h3, h4]
  have hnn : 0 ≤ Γ.scalingSize Ψ W d L :=
    mul_nonneg (mul_nonneg (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _) (pow_nonneg hΨ _))
      (zpow_nonneg (Nat.cast_nonneg _) _)
  have hsz : P.g.scalingSize Ψ W d L = Γ.scalingSize Ψ W d L := by
    simp only [LGraph.scalingSize, hc]
  simp only [LGraph.scalingSizeG, hP, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    hsz]
  exact max_eq_left hnn

end NormalAgree

/-! ## 15. Compiled instances -/

section Instances

/-- Nondegenerate data on three labels: a generic `G`, `M = m I` with `m = 1/2`, a real symmetric `S`. -/
def lwD : LData (Fin 3) where
  G := Matrix.of ![![1, 2, 3], ![4, 5, 6], ![7, 8, 10]]
  M := Matrix.diagonal fun _ => (1 / 2 : ℂ)
  S := Matrix.of ![![1, 1 / 2, 1 / 3], ![1 / 2, 1, 1 / 4], ![1 / 3, 1 / 4, 1]]
  Sp := Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

private theorem lwD_S_real : ∀ i j, star (lwD.S i j) = lwD.S i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lwD]

private theorem lwD_M_diag : ∀ x, lwD.M x x = (1 / 2 : ℂ) := by
  intro x
  simp [lwD]

/-- `f_{01}(G) = 259` on the data `lwD` (the single term `α = 2`: `24 · 259/24`). -/
private theorem lwFxyVal : fxyVal lwD 0 1 = 259 := by
  simp [fxyVal, lwD, Fin.sum_univ_three]
  norm_num

/-- `(eq:p=2graph)` at concrete data: the value of `p2Graph` at `(x, y) = (0, 1)` is
`|f_{xy}|² = 259²` (`p2Graph_val_eq`; the sum over `α ∉ {x, y}` has the one term `α = 2`). -/
private theorem lwP2Graph_val : p2Graph.val lwD ![0, 1] = 67081 := by
  rw [p2Graph_val_eq lwD lwD_S_real 0 1, lwFxyVal]
  norm_num

/-- `figGraph_val` at the data `lwD`. -/
example := figGraph_val lwD 0 1

/-- **A normal graph with a `×`-dotted edge** (`defnlvl0`): external `x = inl 0`, internal `a, b = inr 0,
inr 1`; the solid edges `G_{xa}`, `Ḡ_{xa}` (off-diagonal), the light-weight `(G-M)_{bb}`, the waved edge
`S_{ab}` and the `×`-dotted edge `1_{a≠x}`: `n_S = 3`, `n_W = 1`, `n_V = 2`, `n_M = 1` (the molecule
`{a, b}`), `ord = 3 + 2 (1 - 2) = 1`. -/
def lwNwGraph : LGraph (Fin 1) (Fin 2) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨false, false, .inl 0, .inr 0⟩, ⟨true, true, .inr 1, .inr 1⟩]
  waved := [⟨false, true, .inr 0, .inr 1⟩]
  dotted := [⟨false, .inr 0, .inl 0⟩]
  coeff := 1

/-- The graph `S_{xa} G_{xa}` with `n_W = n_V`: external `x`, internal `a`, one solid edge, one waved
edge and the `×`-dotted edge `1_{a≠x}`. -/
def lwSwGraph : LGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩]
  waved := [⟨false, true, .inl 0, .inr 0⟩]
  dotted := [⟨false, .inr 0, .inl 0⟩]
  coeff := 1

/-- The non-normal graph `∑_a G_{xa} Ḡ_{xa}`: external `x`, internal `a`, no dotted edge. -/
def lwSumGG : LGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨false, false, .inl 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1

/-- The graph `G_{xa}` with a `=`-dotted edge `1_{a=x}`: `∑_a 1_{a=x} G_{xa} = G_{xx}`. -/
def lwEqGraph : LGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩]
  waved := []
  dotted := [⟨true, .inr 0, .inl 0⟩]
  coeff := 1

/-- A graph with no internal vertex: the light-weight-free solid edge `(G-M)_{xy}`. -/
def lwEdgeGraph : LGraph (Fin 2) (Fin 0) where
  solid := [⟨true, true, .inl 0, .inl 1⟩]
  waved := []
  dotted := []
  coeff := 1

-- counters and `ord` of the two probe examples, by `decide`
example : ord p2Graph.counters = 2 := by decide
example : ord figGraph.counters = 4 := by decide
example : p2Graph.scalingOrder = 2 ∧ figGraph.scalingOrder = 4 := by decide
-- the normal graphs
example : p2Graph.Normal := by decide
example : figGraph.Normal := by decide
-- the normal graph with a `×`-dotted edge
example : lwNwGraph.Normal := by decide
example : lwNwGraph.nS = 3 ∧ lwNwGraph.nW = 1 ∧ lwNwGraph.nV = 2 ∧ lwNwGraph.nM = 1 := by decide
example : ord lwNwGraph.counters = 1 := by decide
example : lwSwGraph.Normal := by decide
example : lwSwGraph.nS = 1 ∧ lwSwGraph.nW = 1 ∧ lwSwGraph.nV = 1 ∧ lwSwGraph.nM = 0 := by decide
-- a non-normal graph: `∑_a G_{xa} Ḡ_{xa}` has no `×`-dotted edge, a `=`-dotted edge is not normal
example : ¬ lwSumGG.Normal := by decide
example : ¬ lwEqGraph.Normal := by decide
example : p2Graph.DotWF ∧ figGraph.DotWF ∧ lwNwGraph.DotWF := by decide

-- the dotted edge expansion of `∑_a G_{xa} Ḡ_{xa}`: one pair `{x, a}`, branches `1_{x=a}`, `1_{x≠a}`
example : lwSumGG.dotChoices.map (fun c => (c.1, c.2.map fun e => e.eq)) = [(1, [true]), (1, [false])] := by
  decide
-- the molecules of the figure graph, as connected components of waved and dotted edges
example : figGraph.mol (Sum.inr 0) = {Sum.inr 0, Sum.inr 1, Sum.inr 2} := by decide
example : figGraph.molGraph.Reachable (Sum.inr 0) (Sum.inr 2) :=
  (figGraph.mem_mol_iff _ _).1 (by decide)
example : Nat.card {c : figGraph.Mol // ¬ figGraph.IsExtMol c} = 2 := by
  rw [← figGraph.nM_eq_card]; decide

/-- `∑_a G_{xa} Ḡ_{xa}` at `x = 0` on the data `lwD`: `1 + 4 + 9 = 14`. -/
private theorem lwSumGG_val : lwSumGG.val lwD ![0] = 14 := by
  unfold LGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero]
  simp [lwSumGG, LGraph.term, SEdge.val, lwD, Fin.sum_univ_three, map_ofNat]
  norm_num

/-- The dotted edge partition at concrete data: the value `14` is the value of the linear combination
of normal graphs (so the partition is not empty). -/
example : LComb.val (lwSumGG.partition (1 / 2)) lwD ![0] = 14 := by
  rw [← lwSumGG.val_eq_partition (1 / 2) lwD lwD_M_diag ![0], lwSumGG_val]

example : ∀ P ∈ lwSumGG.partition (1 / 2), P.g.Normal := lwSumGG.partition_normal (1 / 2)

/-- `∑_a 1_{a=x} G_{xa} = G_{xx} = 1` at `x = 0`. -/
private theorem lwEqGraph_val : lwEqGraph.val lwD ![0] = 1 := by
  unfold LGraph.val
  simp only [sum_pi_fin_succ, sum_pi_fin_zero]
  simp [lwEqGraph, LGraph.term, SEdge.val, DEdge.val, lwD]

example : lwEqGraph.mergeP.val lwD ![0] = 1 := by
  rw [lwEqGraph.mergeP_val, lwEqGraph_val]

/-- A graph with no internal vertex: `(G-M)_{01} = 2`. -/
private theorem lwEdgeGraph_val : lwEdgeGraph.val lwD ![0, 1] = 2 := by
  rw [lwEdgeGraph.val_of_isEmpty_prod lwD ![0, 1] finZeroElim]
  simp [lwEdgeGraph, SEdge.val, lwD]

-- packed graphs
example : p2Graph.pack.val lwD ![0, 1] = 67081 := by rw [p2Graph.pack_val, lwP2Graph_val]
-- relabeling the vertices, the labels
example : (p2Graph.relabel (Equiv.sumCongr (finRotate 2) (finRotate 4))).val lwD ![0, 1] =
    p2Graph.val lwD (![0, 1] ∘ finRotate 2) :=
  p2Graph.val_relabel_equiv (finRotate 2) (finRotate 4) lwD ![0, 1]
example : p2Graph.val (lwD.map (finRotate 3)) (finRotate 3 ∘ ![0, 1]) = 67081 :=
  (p2Graph.val_map_equiv (finRotate 3) lwD ![0, 1]).trans lwP2Graph_val
-- disjoint unions: counters, `ord`, value
example : (p2Graph.disjUnion lwNwGraph).nS = 9 ∧ (p2Graph.disjUnion lwNwGraph).nW = 3 ∧
    (p2Graph.disjUnion lwNwGraph).nV = 6 ∧ (p2Graph.disjUnion lwNwGraph).nM = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LGraph.nS_disjUnion]; decide
  · rw [LGraph.nW_disjUnion]; decide
  · rw [LGraph.nV_disjUnion]; decide
  · rw [LGraph.nM_disjUnion]; decide
example : ord (p2Graph.disjUnion lwNwGraph).counters = 3 := by
  rw [LGraph.ord_disjUnion]; decide
example : (p2Graph.disjUnion lwEdgeGraph).val lwD (Sum.elim ![0, 1] ![0, 1]) = 67081 * 2 := by
  rw [LGraph.val_disjUnion, lwP2Graph_val, lwEdgeGraph_val]
-- scaling size at `d = 3`, `W = 2`, `L = 3`, `Ψ = 1/2`
example : p2Graph.scalingSize (1 / 2) 2 3 3 = 729 := by
  have h := p2Graph_counters
  simp only [LGraph.scalingSize, LGraph.counters, Counters.scalingSize, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num
example : figGraph.scalingSize (1 / 2) 2 3 3 = 729 / 4 := by
  have h := figGraph_counters
  simp only [LGraph.scalingSize, LGraph.counters, Counters.scalingSize, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num
example : p2Graph.counters.scalingSize (1 / 2) 2 3 3 =
    (((3 : ℕ) : ℝ) ^ 3) ^ p2Graph.counters.nM * (1 / 2 : ℝ) ^ (ord p2Graph.counters) *
      (((2 : ℕ) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ 2) ^ ((p2Graph.counters.nV : ℤ) - p2Graph.counters.nW) :=
  p2Graph.counters.scalingSize_eq 2 3 3 (by norm_num)
example : (((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ 1 / 2) :=
  (one_le_pow_mul_sq_iff 2 3 (by norm_num) (by norm_num)).2 (by norm_num)
example : lwSwGraph.scalingSize (1 / 2) 2 3 3 ≤ (((3 : ℕ) : ℝ) ^ 3) ^ lwSwGraph.nM * (1 / 2 : ℝ) ^ (ord lwSwGraph.counters) :=
  lwSwGraph.counters.scalingSize_le 2 3 3 (by norm_num) (by norm_num) (by decide)

-- the general scaling order and size of a normal graph are those of the normal graph
example : lwNwGraph.scalingOrderG (1 / 2) = ((1 : ℤ) : WithTop ℤ) := by
  rw [lwNwGraph.scalingOrderG_of_normal (1 / 2) (by decide) (by decide)]
  have : lwNwGraph.scalingOrder = 1 := by decide
  rw [this]
example : lwNwGraph.scalingSizeG (1 / 2) (1 / 2) 2 3 3 = 27 := by
  rw [lwNwGraph.scalingSizeG_of_normal (1 / 2) (by decide) (by decide) (by norm_num)]
  have h : lwNwGraph.nS = 3 ∧ lwNwGraph.nW = 1 ∧ lwNwGraph.nV = 2 ∧ lwNwGraph.nM = 1 := by decide
  simp only [LGraph.scalingSize, LGraph.counters, Counters.scalingSize, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num

/-- A graph with a weight: `G_{xx}` (no circle) at an external vertex. -/
def lwLoopGraph : LGraph (Fin 1) (Fin 0) where
  solid := [⟨true, false, .inl 0, .inl 0⟩]
  waved := []
  dotted := []
  coeff := 1

-- the expansion of the dotted edges and the weight split at concrete data
example : lwSumGG.val lwD ![0] = (lwSumGG.dotChoices.map fun c => (lwSumGG.withDots c).val lwD ![0]).sum :=
  lwSumGG.val_eq_sum_dotChoices lwD ![0]
private theorem lwLoopGraph_val : lwLoopGraph.val lwD ![0] = 1 := by
  rw [lwLoopGraph.val_of_isEmpty_prod lwD ![0] finZeroElim]
  simp [lwLoopGraph, SEdge.val, lwD]
example : ((lwLoopGraph.splitWeights (1 / 2)).map fun g => g.val lwD ![0]).sum = 1 := by
  rw [← lwLoopGraph.val_splitWeights (1 / 2) lwD lwD_M_diag, lwLoopGraph_val]
example : ((lwEqGraph.mergeSplitP (1 / 2)).map fun P => P.val lwD ![0]).sum = 1 := by
  rw [lwEqGraph.mergeSplitP_val (1 / 2) lwD lwD_M_diag, lwEqGraph_val]
example : lwEqGraph.val lwD ((fun _ => (0 : Fin 3)) ∘ lwEqGraph.extMap) =
    lwEqGraph.merge.val lwD (fun _ => 0) := lwEqGraph.val_eq_merge_val lwD (fun _ => 0)
-- the molecules and the relabeling at concrete graphs
example : figGraph.molOf (Sum.inr 0) = figGraph.molOf (Sum.inr 2) :=
  (figGraph.molOf_eq_iff _ _).2 (by decide)
example : ¬ figGraph.IsExtMol (figGraph.molOf (Sum.inr 0)) :=
  (figGraph.forall_mol_isRight_iff (Sum.inr 0)).1 (by decide)
example : (Sum.inr 2 : Fin 2 ⊕ Fin 6) ∈ figGraph.step^[Fintype.card (Fin 2 ⊕ Fin 6)] {Sum.inr 0} :=
  (figGraph.mem_iterate_iff le_rfl _ _).2 ((figGraph.mem_mol_iff _ _).1 (by decide))
example : (p2Graph.relabel (Equiv.sumCongr (finRotate 2) (finRotate 4))).nM = 2 := by
  rw [(p2Graph.counters_relabel_equiv (Equiv.sumCongr (finRotate 2) (finRotate 4))
    (by intro v; rcases v with a | b <;> rfl)).2.2.2]
  decide
-- the minimum over the partition: a lower bound for `lwNwGraph`
example : ((1 : ℤ) : WithTop ℤ) ≤ lwNwGraph.scalingOrderG (1 / 2) := by
  refine (lwNwGraph.le_scalingOrderG_iff (1 / 2) 1).2 fun P hP => ?_
  obtain ⟨Q, hQ, h1, h2, h3, h4⟩ := lwNwGraph.partition_of_normal (1 / 2) (by decide) (by decide)
  rw [hQ, List.mem_singleton] at hP
  subst hP
  have h : lwNwGraph.nS = 3 ∧ lwNwGraph.nW = 1 ∧ lwNwGraph.nV = 2 ∧ lwNwGraph.nM = 1 := by decide
  simp only [LGraph.scalingOrder, LGraph.counters, ord, h1, h2, h3, h.1, h.2.1, h.2.2.1]
  norm_num
example : lwNwGraph.scalingSizeG (1 / 2) (1 / 2) 2 3 3 ≤ 27 := by
  refine ((lwNwGraph.scalingSizeG_le_iff (1 / 2) (1 / 2) 2 3 3 27).2 ⟨by norm_num, fun P hP => ?_⟩)
  obtain ⟨Q, hQ, h1, h2, h3, h4⟩ := lwNwGraph.partition_of_normal (1 / 2) (by decide) (by decide)
  rw [hQ, List.mem_singleton] at hP
  subst hP
  have h : lwNwGraph.nS = 3 ∧ lwNwGraph.nW = 1 ∧ lwNwGraph.nV = 2 ∧ lwNwGraph.nM = 1 := by decide
  simp only [LGraph.scalingSize, LGraph.counters, Counters.scalingSize, h1, h2, h3, h4, h.1, h.2.1,
    h.2.2.1, h.2.2.2]
  norm_num

end Instances

end RBM.Graph
