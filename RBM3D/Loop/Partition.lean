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

theorem crossing_comm {n : ℕ} (e f : Fin n × Fin n) : Crossing e f ↔ Crossing f e := by
  unfold Crossing; tauto

theorem not_crossing_self {n : ℕ} (e : Fin n × Fin n) : ¬Crossing e e := by
  unfold Crossing; omega

theorem mem_TSP {n : ℕ} {F : Finset (Fin n × Fin n)} :
    F ∈ TSP n ↔ F ⊆ diagonals n ∧ CrossingFree F := by
  simp [TSP]

theorem empty_mem_TSP (n : ℕ) : (∅ : Finset (Fin n × Fin n)) ∈ TSP n := by
  simp [mem_TSP, CrossingFree]

/-- A triangle has no diagonals: the only canonical partition is the star. -/
theorem TSP_three : TSP 3 = {∅} := by decide

/-- The quadrilateral has three canonical partitions: the star and the two single
diagonals, which cross each other and so cannot coexist. -/
theorem TSP_four : TSP 4 = {∅, {(0, 2)}, {(1, 3)}} := by decide

/-- The counts are the small Schröder numbers `1, 3, 11, 45, …`, which is what the
dissections of a polygon are counted by. -/
theorem card_TSP_five : (TSP 5).card = 11 := by decide

/-- **Non-crossing ⇒ separable.**  A diagonal `f` that does not cross `e = (i, j)` lies in
the left arc `[i, j]` or in the right arc `[j, n-1] ∪ [0, i]`; this is what makes the split
below well defined on crossing-free sets. -/
theorem noncrossing_split {n : ℕ} {e f : Fin n × Fin n} (h : ¬Crossing e f) :
    (e.1 ≤ f.1 ∧ f.2 ≤ e.2) ∨ (f.2 ≤ e.1 ∨ e.2 ≤ f.1 ∨ (f.1 ≤ e.1 ∧ e.2 ≤ f.2)) := by
  simp only [Crossing, not_or, not_and, not_lt] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Fin.le_def, Fin.lt_def] at h1 h2 ⊢
  omega

/-- Both pieces of a split along a diagonal are strictly smaller polygons. -/
theorem isDiag_split_lt {n : ℕ} {i j : Fin n} (h : IsDiag n i j) :
    j.val - i.val + 1 < n ∧ n - (j.val - i.val) + 1 < n := by
  obtain ⟨hij, hadj, hwrap⟩ := h
  have := j.isLt
  rw [Fin.lt_def] at hij
  omega

/-- Re-index a region of the right piece of a split at `(i, j)`. -/
def reindexR (n j : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let k := (p.1 + n - j) % n
  let l := (p.2 + n - j) % n
  (min k l, max k l)

/-- The diagonals that go to the left piece of the split at `(i, j)`, re-indexed. -/
def leftPairs (i j : ℕ) (F : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (F.filter fun p => i ≤ p.1 ∧ p.2 ≤ j).map fun p => (p.1 - i, p.2 - i)

/-- The diagonals that go to the right piece of the split at `(i, j)`, re-indexed. -/
def rightPairs (n i j : ℕ) (F : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (F.filter fun p => ¬(i ≤ p.1 ∧ p.2 ≤ j)).map (reindexR n j)

theorem length_leftPairs_le (i j : ℕ) (F : List (ℕ × ℕ)) :
    (leftPairs i j F).length ≤ F.length := by
  rw [leftPairs, List.length_map]
  exact List.length_filter_le _ _

theorem length_rightPairs_le (n i j : ℕ) (F : List (ℕ × ℕ)) :
    (rightPairs n i j F).length ≤ F.length := by
  rw [rightPairs, List.length_map]
  exact List.length_filter_le _ _

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

/-- The star tree, the canonical partition with no diagonals:
`Σ_b ∏_i Θ^(σ_i,σ_{i+1})_t(a_i, b)`. -/
noncomputable def starGamma {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  ∑ b : Zd d L, ∏ i : Fin n, thetaEdge d L g m t (σ i) (σ (i + 1)) (a i) b

/-- The value of a polygon with region charges `rs`, vertices `vs` (each a label together
with its boundary matrix) and diagonal list `F`.

* `F = []` is the star, `Σ_b ∏_k (M_k)_{a_k b}`;
* a diagonal `(i, j)` splits the polygon into the left piece (regions `i, …, j`) and the
  right piece (regions `j, …, n-1, 0, …, i`), closed up by a new vertex carrying the label
  `y`; the left copy carries `(Θ^(σ_i,σ_j)_t - I)ᵀ` and the right one the identity, which
  together produce the internal edge `(f-internal)` between the two centres;
* a head that is not a diagonal is skipped.

Termination: a diagonal has `j - i ≥ 2` and is not the wrap-around pair, so both pieces
have fewer regions (`isDiag_split_lt`). -/
noncomputable def polyVal (m : Bool → ℂ) (t : ℝ) :
    List Bool → List (Zd d L × Matrix (Zd d L) (Zd d L) ℂ) → List (ℕ × ℕ) → ℂ
  | _, vs, [] => ∑ b : Zd d L, (vs.map fun v => v.2 v.1 b).prod
  | rs, vs, (i, j) :: F =>
    if h : i + 2 ≤ j ∧ j < rs.length ∧ ¬(i = 0 ∧ j = rs.length - 1) then
      ∑ y : Zd d L,
        polyVal m t ((rs.drop i).take (j - i + 1))
          ((vs.drop i).take (j - i) ++
            [(y, (thetaEdge d L g m t (rs.getD i false) (rs.getD j false) - 1).transpose)])
          (leftPairs i j F) *
        polyVal m t (rs.drop j ++ rs.take (i + 1)) (vs.drop j ++ vs.take i ++ [(y, 1)])
          (rightPairs rs.length i j F)
    else polyVal m t rs vs F
termination_by rs _ F => rs.length + F.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_append,
    List.length_cons]
  · have := length_leftPairs_le i j F
    omega
  · have := length_rightPairs_le rs.length i j F
    omega
  · omega

/-- The polygon `P_a` of `def:canpnical_part`: vertex `k` carries the label `a_k` and the
boundary propagator `Θ^(σ_k,σ_{k+1})_t` of `(f-external)`. -/
noncomputable def bdList (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (Zd d L)) :
    List (Zd d L × Matrix (Zd d L) (Zd d L) ℂ) :=
  (List.range σ.length).map fun k =>
    (a.getD k 0, thetaEdge d L g m t (σ.getD k false) (σ.getD ((k + 1) % σ.length) false))

/-- The value `Σ_b ∏_e f_{t,σ}(e)` of the tree with diagonal list `F`. -/
noncomputable def treeVal (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (Zd d L))
    (F : List (ℕ × ℕ)) : ℂ :=
  if σ.length ≤ 2 then
    thetaEdge d L g m t (σ.getD 0 false) (σ.getD 1 false) (a.getD 0 0) (a.getD 1 0)
  else polyVal d L g m t σ (bdList d L g m t σ a) F

/-- The diagonals of `F` in lexicographic order, so that the value of a `Finset` of
diagonals is well defined without choosing a pivot. -/
def diagList {n : ℕ} (F : Finset (Fin n × Fin n)) : List (ℕ × ℕ) :=
  ((F.image fun p => p.1.val * n + p.2.val).sort (· ≤ ·)).map fun c => (c / n, c % n)

/-- `Σ_{Γ ∈ TSP(P_a)} Σ_b ∏_e f_{t,σ}(e)`, the sum over canonical partitions. -/
noncomputable def treeSum (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (Zd d L)) : ℂ :=
  ∑ F ∈ TSP σ.length, treeVal d L g m t σ a (diagList F)

/-- **`(M-graph-value-unsummed)`**: `Γ^(n)_{t,σ,a} = (∏_i m(σ_i)) Σ_b ∏_e f_{t,σ}(e)`. -/
noncomputable def GammaN {n : ℕ} (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) (F : Finset (Fin n × Fin n)) : ℂ :=
  (∏ i : Fin n, m (σ i))
    * treeVal d L g m t (List.ofFn σ) (List.ofFn a) (diagList F)

/-- The sum of `Γ^(n)` over all canonical partitions -- the right-hand side of the tree
representation `eq_Ktree`, before the `W^{-d(n-1)}` prefactor (`docs/QUEUE.md`, Q15). -/
noncomputable def GammaSum {n : ℕ} (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  ∑ F ∈ TSP n, GammaN d L g m t σ a F

variable {d L g}

/-- The star is the `F = ∅` term. -/
theorem treeVal_nil_eq_polyVal (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (Zd d L))
    (hσ : 2 < σ.length) :
    treeVal d L g m t σ a [] = polyVal d L g m t σ (bdList d L g m t σ a) [] := by
  rw [treeVal, ite_eq_right (by omega)]

/-- **Acceptance.**  At `n = 4` the star tree (no diagonals) is the value the paper's
`(f-external)` edges give directly: `Σ_b ∏_i Θ^(σ_i,σ_{i+1})_t(a_i, b)`. -/
theorem treeVal_four_nil (m : Bool → ℂ) (t : ℝ) (σ : Fin 4 → Bool) (a : Fin 4 → Zd d L) :
    treeVal d L g m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3] []
      = starGamma d L g m t σ a := by
  have hbd : bdList d L g m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3]
      = [(a 0, thetaEdge d L g m t (σ 0) (σ 1)), (a 1, thetaEdge d L g m t (σ 1) (σ 2)),
        (a 2, thetaEdge d L g m t (σ 2) (σ 3)), (a 3, thetaEdge d L g m t (σ 3) (σ 0))] := by
    simp only [bdList, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil]
    rfl
  rw [treeVal, ite_eq_right (by simp), hbd, polyVal, starGamma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Fin.prod_univ_four,
    show ((0 : Fin 4) + 1) = 1 from rfl, show ((1 : Fin 4) + 1) = 2 from rfl,
    show ((2 : Fin 4) + 1) = 3 from rfl, show ((3 : Fin 4) + 1) = 0 from rfl]
  ring

/-- With `n ≥ 3` fixed, `GammaSum` has one summand per canonical partition. -/
theorem GammaSum_eq_sum {n : ℕ} (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) :
    GammaSum d L g m t σ a = ∑ F ∈ TSP n, GammaN d L g m t σ a F := rfl

end RBM.Loop
