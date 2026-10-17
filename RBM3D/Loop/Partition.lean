/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic
import RBM3D.Propagator.Props4

/-!
# Canonical tree partitions `TSP(P_a)` and the value `Γ^(n)_{t,σ,a}`

Appendix A.5 (`Sec:CalK`), `def:canpnical_part` and the definition of the edge values that
follows it.  A canonical partition of the oriented polygon `P_a` with vertices
`a = (a_1, …, a_n)` cuts it into sub-polygons, one per side, with each vertex `a_k` lying in
exactly two regions `R_k`, `R_{k+1}`; removing the `n` sides leaves a tree whose leaves are
the vertices of `P_a`, and `TSP(P_a)` is the set of those trees.  Given `σ ∈ {+,-}^n` the
region `R_k` carries the charge `σ_k`, and the edges take the values

* `(f-external)`  `f_{t,σ}(a_k, b) = Θ^(σ_k,σ_{k+1})_t(a_k, b)` for an external edge;
* `(f-internal)`  `f_{t,σ}(b₁, b₂) = (Θ^(σ_k,σ_l)_t - I)(b₁, b₂)` for an internal edge
  between the regions `R_k` and `R_l`;

and `(M-graph-value-unsummed)` assigns to the tree the value

  `Γ^(n)_{t,σ,a} = (∏_i m(σ_i)) · Σ_b ∏_e f_{t,σ}(e)`,

the sum being over the internal vertices.  The paper calls this representation
"dimension-independent", and indeed the combinatorics below is the one the sister project
`RBM1D` uses (`RBM1D/Loop/Crossing.lean`, `RBM1D/Loop/Tree.lean`); only the index type
changes, from `ZMod L` to `Zd d L`, and the propagator carries the coupling `g`.  Keeping
the two projects' data structures identical is what will make the tree representation
`eq_Ktree` portable (`docs/QUEUE.md`, Q15).

## Modelling

The planar geometry of `def:canpnical_part` is not formalized.  As in `RBM1D` (and recorded
there), a tree is identified with its set of *diagonals*: by the combinatorial half of the
definition, a canonical partition is determined by which non-adjacent pairs of vertices are
joined, and a set of diagonals arises from a partition exactly when no two of its diagonals
cross.  `RBM.Loop.TSP n` is therefore *defined* as the crossing-free sets of diagonals, and
the value of a tree is computed by recursion on that set: splitting along a diagonal cuts
the polygon into two smaller ones joined at a new internal vertex, which is exactly the
internal edge `(Θ - I)` of `(f-internal)`.

## Main definitions

* `RBM.Loop.IsDiag`, `RBM.Loop.diagonals`, `RBM.Loop.Crossing`, `RBM.Loop.TSP`
* `RBM.Loop.thetaEdge` : `Θ^(σ_k,σ_l)_t`, the edge propagator
* `RBM.Loop.starGamma` : the star tree (no diagonals)
* `RBM.Loop.polyVal`, `RBM.Loop.treeVal`, `RBM.Loop.treeSum` : the value of a tree and the
  sum over `TSP(P_a)`
* `RBM.Loop.GammaN` : `Γ^(n)_{t,σ,a}` of `(M-graph-value-unsummed)`, with the `∏ m(σ_i)`
-/

namespace RBM.Loop

open Finset

/-! ### The combinatorics of `TSP(P_a)` -/

/-- `{i, j}` (with `i < j`) is a diagonal of the `n`-gon: the vertices are not adjacent
modulo `n`.  `{0, n-1}` is a side, not a diagonal. -/
def IsDiag (n : ℕ) (i j : Fin n) : Prop :=
  i < j ∧ j.val ≠ i.val + 1 ∧ ¬(i.val = 0 ∧ j.val = n - 1)

instance (n : ℕ) (i j : Fin n) : Decidable (IsDiag n i j) := by
  unfold IsDiag; infer_instance

/-- The diagonals of the `n`-gon, as ordered pairs `(i, j)` with `i < j`. -/
def diagonals (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => IsDiag n p.1 p.2

/-- Two diagonals cross if `i < k < j < l` or `k < i < l < j`.  Diagonals sharing an
endpoint do not cross. -/
def Crossing {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨ (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

instance {n : ℕ} (e f : Fin n × Fin n) : Decidable (Crossing e f) := by
  unfold Crossing; infer_instance

/-- No two diagonals of `F` cross. -/
def CrossingFree {n : ℕ} (F : Finset (Fin n × Fin n)) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, ¬Crossing e f

instance {n : ℕ} (F : Finset (Fin n × Fin n)) : Decidable (CrossingFree F) := by
  unfold CrossingFree; infer_instance

/-- `TSP(P_a)` for the `n`-gon: the crossing-free sets of diagonals. -/
def TSP (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  (diagonals n).powerset.filter CrossingFree

theorem not_crossing_self {n : ℕ} (e : Fin n × Fin n) : ¬Crossing e e := by
  unfold Crossing; omega

theorem mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} :
    F ∈ TSP n ↔ F ⊆ diagonals n ∧ CrossingFree F := by
  simp [TSP]

theorem empty_mem_TSP (n : ℕ) : (∅ : Finset (Fin n × Fin n)) ∈ TSP n := by
  simp [mem_TSP, CrossingFree]

/-- A triangle has no diagonals: the only canonical partition is the star. -/
theorem TSP_three : TSP 3 = {∅} := by decide

/-! ### Edge values -/

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The propagator of an edge between regions with charges `s`, `s'`:
`Θ^(s,s')_t = Theta d L g (t · m(s) m(s'))`. -/
noncomputable def thetaEdge (m : Bool → ℂ) (t : ℝ) (s s' : Bool) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Theta d L g ((t : ℂ) * (m s * m s'))

theorem thetaEdge_comm (m : Bool → ℂ) (t : ℝ) (s s' : Bool) :
    thetaEdge d L g m t s s' = thetaEdge d L g m t s' s := by
  rw [thetaEdge, thetaEdge, mul_comm (m s)]

end RBM.Loop
