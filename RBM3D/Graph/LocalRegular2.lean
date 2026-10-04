/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular

/-!
# LW-10b: `lem:localregular`, second half: property (4) and the assembly of (1)-(5) (T2151)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (cited `7_8:line`;
`lem:localregular`) and its proof `paper/tex/B_graphical_lemmas.tex:172-199` (cited `B:line`).
Design: T2040 (row LW-10), split by DECISIONS §42 and §47: the first half is the merged
`Graph/LocalRegular.lean` (T2142: `fxyPowGraph`, the predicates `PGraph.LocReg1`-`LocReg6`, the Hall
invariant `PGraph.PathInv`, `lw_localregular_expansion`).  Property (6) (`7_8:815-818`, `B:200-278`)
is **not** in this file: it moved to LW-10c (DECISIONS §47).

## Why a new invariant

Property (4) (`B:193-199`) says that every internal molecule is visited by two different walks of
the one family that carries (3) and (5).  The paper's argument tracks the labelled correspondence
"walk `i` ↔ the molecule of `α_i`": a molecule that merged two original ones is visited by both
walks, and a molecule that is still `𝓜_i` "must pull in some `Ḡ` edge", which brings in a second
walk.  The merged Hall invariant `PGraph.PathInv` does not carry the labels (T2142 report (d) 1) and
cannot give (4).  Here the labels are replaced by the *colour* of the walks.

## The coloured invariant (`PGraph.PathInv2`, `LGraph.localReg2_PathFam`, `localReg2_Fam`)

`PathInv2 p Q`: there are `p` walks `W_i` in the molecular multigraph from the molecule of
`x = Q.ext 0` to that of `y = Q.ext 1` (a walk is a list of steps `(a, b)`, as in
`localReg_StepWalk`; loop steps are free) and colours `col i : Bool`, such that

* (a) *exactness*: the non-loop steps of the walks, each carrying the colour of its walk, are
  exactly the non-loop solid edges of `Q`, each carrying its colour (equality of multisets of
  coloured unordered pairs of molecules: every molecular edge lies on exactly one walk, and a walk
  uses only edges of its colour);
* (b) *Hall*: every set `A` of internal molecules is visited by at least `|A|` walks;
* (c) *colour-visit clause*: if a solid edge of colour `σ` (a loop, or an edge inside a molecule,
  included) has an end in the molecule `C`, then some walk of colour `σ` visits `C`.

It holds at `fxyPowGraph p` (`fxyPowGraph_pathInv2`: walk `i` is `x → 𝓜_i → y` of the colour of the
block `i`) and passes along every `LocStep` (`pathInv2_locStep`).  A step is a twisted `owxExt` term
followed by the dotted edge partition; the proof has the architecture of `pathInv_locStep`.  The new
facts are the following.

* The generic lemmas of the merged file are redone for coloured, exact families (§1):
  `localReg2_Fam.map` (the walks are mapped along a map of the nodes that is onto the internal
  nodes), `of_add_diag`/`add_diag` (loops are dropped; a loop whose colour is present may be added),
  `flip` (a global flip of the colours, the twist `(c, t)` of the selected edge), and
  `localReg2_Fam.thr`: the edge `(σ, {a, b})` is replaced by `(σ, {a, X})`, `(σ, {X, b})`, the walk
  that used it passes through `X`.  **If the edge is a loop or lies inside a molecule (`a = b`)**
  the two new edges are a closed detour `a → X → a` that is inserted into a walk of colour `σ`
  visiting `a`; such a walk exists by (c).  This is the case of `B:197` ("the two new edges
  between `𝓜_i` and `𝓜_j` can be incorporated into path `𝔓_j`") that the merged invariant does not
  see.
* The replacements of the 17 output terms of `(Owx)`, `(Oe1x)`, `(Oe2x)` (§3) are
  `localReg2_VRepl.same` (the molecular edges are unchanged up to loops) and `localReg2_VRepl.deriv`
  (an edge `e` is replaced by the two edges of its derivative `owxDE`, of the colour of `e`, through
  the molecule of `x`); the new loops (the weights `Ǧ_{αα}`, `Ǧ_{ββ}` and the edge `G_{αx}` inside
  `𝓜(x)`) carry the colour of an edge that is removed or kept at `𝓜(x)` (the hypotheses `hcov`,
  discharged term by term), so (c) is kept.  The terms `(Owx)` T1, `(Oe1x)` `Ǧ_{αα}` and `R3` keep
  the selected edge, which supplies the colour (`lvl1_mem_split_fst`, `localReg2_mem_frame`,
  `localReg2_mem_frame2`).

## At a locally standard graph (`LGraph.localReg2_present_of_locStd`, `PGraph.PathInv2.locReg345`)

Let `C` be an internal molecule.  Hall gives a walk through `C`; its first step into `C` is an edge
between different molecules, so some vertex `v` of `C` has a solid edge.  `v` is standard neutral
(`LocStd`, `deflvl1`): it has one blue and one red edge, so both colours are present at `C`, and (c)
gives a blue and a red walk through `C`; they are different walks.  The same family, with its loop
steps deleted (`localReg_stepStrip`), is the family of (3), (4), (5).

## Contents (namespace `RBM.Graph`; helpers carry the prefix `localReg2_`)

1. Coloured exact families (`localReg2_Fam`) and their stage lemmas: `map`, `of_add_diag`,
   `add_diag`, `flip`, `thr`, `repl_same`, `repl_deriv`.
2. The graph level: `SEdge.localReg2_cends`, `LGraph.localReg2_PathFam`,
   `LGraph.localReg2_pathFam_map`, `LGraph.localReg2_pathFam_partition`,
   `LGraph.localReg2_pathFam_stage1`, `localReg2_pathFam_term`; the replacements
   `localReg2_VRepl.same/deriv`.
3. The 17 output terms (`localReg2_pathFam_owxT1`-`T4`, `oe1xOwx`, `oe1xD`, `oe1xP5/P3/P6/P4`,
   `oe2xR2`-`R8`) and `localReg2_pathFam_oe1xDs`.
4. `PGraph.PathInv2`, `pathInv2_locStep`.
5. The starting graph: `fxyPowGraph_pathInv2`.
6. `PGraph.PathInv2.locReg345` (the invariant at a locally standard graph gives (3), (4), (5) for
   one family of walks).
7. `lw_localregular_upto5`: `(eq:local_Gs)` and, for every `Q ∈ outs`, `Q.LocReg1 ∧ Q.LocReg2 p ∧
   Q.LocReg345 p`.
8. Compiled instances: `fxyPowGraph 2`, `fxyPowGraph 4`, one `LocStep`, a small locally standard
   graph with two walks through one internal molecule, `lw_localregular_upto5` at `p = 2` with the
   merged instance data.

## Differences from the paper and the ticket (delta candidates, numbered by the dispatcher)

* `T2151d`: property (4) is proved from the coloured invariant (exact edge partition, walks of one
  colour, colour-visit clause) and not from the labelled correspondence "walk `i` ↔ `𝓜_i`" of
  `B:178-199`; the invariant is stronger than (3)-(5), and holds with walks (not simple paths) and
  without `(eq:far_ab)` (as `T2142a`).
* `T2151e`: the case of `B:197` in which a pulled edge lies inside a molecule (or is a weight)
  is the closed detour of `localReg2_Fam.thr`; it needs the colour-visit clause (c) to be part of
  the invariant, since an edge that is on no walk (a loop, an edge inside a molecule) carries no
  walk of its own.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
set_option linter.style.openClassical false

noncomputable section
open Classical

namespace RBM.Graph

/-! ## 1. Coloured exact families of walks (abstract)

The nodes `N` are the molecules, the budget is a multiset of coloured unordered pairs of nodes (the solid edges between molecules, with
their colours).  The walks, `localReg_StepWalk`, `localReg_stepEdges`, `localReg_StepWalk.Visits` are those of `Graph/LocalRegular.lean`. -/

section Walks2

variable {N : Type*}

/-- The coloured steps of a family of walks: a step of the walk `i` carries the colour `col i`. -/
def localReg2_stepMS {p : ℕ} (col : Fin p → Bool) (W : Fin p → List (N × N)) : Multiset (Bool × Sym2 N) :=
  ∑ i, (localReg_stepEdges (W i)).map fun s => (col i, s)

/-- The non-diagonal part of a coloured multiset of unordered pairs. -/
def localReg2_offDiag (m : Multiset (Bool × Sym2 N)) : Multiset (Bool × Sym2 N) := m.filter fun s => ¬ s.2.IsDiag

/-- The colour `σ` is present at the node `C`: some edge of colour `σ` has `C` as an end (loops included). -/
def localReg2_present (B : Multiset (Bool × Sym2 N)) (C : N) (σ : Bool) : Prop := ∃ s ∈ B, s.1 = σ ∧ C ∈ s.2

/-- The image of a coloured multiset along a map of the nodes. -/
def localReg2_mapMS {N' : Type*} (ψ : N → N') (B : Multiset (Bool × Sym2 N)) : Multiset (Bool × Sym2 N') :=
  B.map (Prod.map id (Sym2.map ψ))

/-- **A coloured exact family of `p` walks from `u` to `v`** with the coloured budget `B`: the walk `i` has the colour `col i`; the
non-loop steps of the walks, with the colours of their walks, are exactly the non-loop edges of `B`; the Hall condition holds for the
nodes `Int`; and whenever an edge of colour `σ` has an end `C` (a loop or an edge inside a node included), some walk of colour `σ`
visits `C`. -/
def localReg2_Fam (p : ℕ) (u v : N) (Int : N → Prop) (B : Multiset (Bool × Sym2 N)) : Prop :=
  ∃ (W : Fin p → List (N × N)) (col : Fin p → Bool),
    (∀ i, localReg_StepWalk u v (W i)) ∧
    localReg2_offDiag (localReg2_stepMS col W) = localReg2_offDiag B ∧
    (∀ A : Finset N, (∀ c ∈ A, Int c) →
      A.card ≤ (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits u (W i) c).card) ∧
    (∀ C σ, localReg2_present B C σ → ∃ i, col i = σ ∧ localReg_StepWalk.Visits u (W i) C)

theorem localReg2_offDiag_add (a b : Multiset (Bool × Sym2 N)) :
    localReg2_offDiag (a + b) = localReg2_offDiag a + localReg2_offDiag b := by
  unfold localReg2_offDiag; exact Multiset.filter_add _ _ _

theorem localReg2_offDiag_of_diag {a : Multiset (Bool × Sym2 N)} (h : ∀ s ∈ a, s.2.IsDiag) : localReg2_offDiag a = 0 := by
  unfold localReg2_offDiag; exact Multiset.filter_eq_nil.2 fun s hs => not_not.2 (h s hs)

theorem localReg2_offDiag_eq_self {a : Multiset (Bool × Sym2 N)} (h : ∀ s ∈ a, ¬ s.2.IsDiag) : localReg2_offDiag a = a := by
  unfold localReg2_offDiag; exact Multiset.filter_eq_self.2 h

theorem localReg2_mem_offDiag {m : Multiset (Bool × Sym2 N)} {s : Bool × Sym2 N} :
    s ∈ localReg2_offDiag m ↔ s ∈ m ∧ ¬ s.2.IsDiag := Multiset.mem_filter

theorem localReg2_offDiag_sum {ι : Type*} (s : Finset ι) (f : ι → Multiset (Bool × Sym2 N)) :
    localReg2_offDiag (∑ i ∈ s, f i) = ∑ i ∈ s, localReg2_offDiag (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localReg2_offDiag]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, localReg2_offDiag_add, ih]

theorem localReg2_mapMS_add {N' : Type*} (ψ : N → N') (a b : Multiset (Bool × Sym2 N)) :
    localReg2_mapMS ψ (a + b) = localReg2_mapMS ψ a + localReg2_mapMS ψ b := Multiset.map_add _ _ _

/-- A map of the nodes keeps the non-diagonal parts equal. -/
theorem localReg2_offDiag_map_congr {N' : Type*} (ψ : N → N') {m₁ m₂ : Multiset (Bool × Sym2 N)}
    (h : localReg2_offDiag m₁ = localReg2_offDiag m₂) :
    localReg2_offDiag (localReg2_mapMS ψ m₁) = localReg2_offDiag (localReg2_mapMS ψ m₂) := by
  have key : ∀ m : Multiset (Bool × Sym2 N), localReg2_offDiag (localReg2_mapMS ψ m) =
      ((localReg2_offDiag m).filter fun s => ¬ (Sym2.map ψ s.2).IsDiag).map (Prod.map id (Sym2.map ψ)) := by
    intro m
    unfold localReg2_offDiag localReg2_mapMS
    rw [Multiset.filter_map, Multiset.filter_filter]
    congr 1
    refine Multiset.filter_congr fun s _ => ?_
    simp only [Function.comp_apply, Prod.map_snd]
    constructor
    · intro hs
      exact ⟨hs, fun hd => hs hd.map⟩
    · exact fun hs => hs.1
  rw [key, key, h]


theorem localReg2_stepMS_map {N' : Type*} (ψ : N → N') {p : ℕ} (col : Fin p → Bool) (W : Fin p → List (N × N)) :
    localReg2_stepMS col (fun i => (W i).map (Prod.map ψ ψ)) = localReg2_mapMS ψ (localReg2_stepMS col W) := by
  unfold localReg2_stepMS localReg2_mapMS
  have h := map_sum (Multiset.mapAddMonoidHom (Prod.map id (Sym2.map ψ)))
    (fun i => (localReg_stepEdges (W i)).map fun s => (col i, s)) Finset.univ
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [localReg_stepEdges_map, Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
  rfl

theorem localReg2_present_add_left {B D : Multiset (Bool × Sym2 N)} {C : N} {σ : Bool} (h : localReg2_present B C σ) :
    localReg2_present (B + D) C σ := by
  obtain ⟨s, hs, h1, h2⟩ := h
  exact ⟨s, Multiset.mem_add.2 (Or.inl hs), h1, h2⟩

theorem localReg2_present_add_right {B D : Multiset (Bool × Sym2 N)} {C : N} {σ : Bool} (h : localReg2_present D C σ) :
    localReg2_present (B + D) C σ := by
  obtain ⟨s, hs, h1, h2⟩ := h
  exact ⟨s, Multiset.mem_add.2 (Or.inr hs), h1, h2⟩

/-- **The family is mapped along a map of the nodes** that is onto the internal nodes from internal ones. -/
theorem localReg2_Fam.map {N' : Type*} (ψ : N → N') {p : ℕ} {u v : N} {Int : N → Prop} {Int' : N' → Prop}
    {B : Multiset (Bool × Sym2 N)} (hI : ∀ c', Int' c' → ∃ c, Int c ∧ ψ c = c') (h : localReg2_Fam p u v Int B) :
    localReg2_Fam p (ψ u) (ψ v) Int' (localReg2_mapMS ψ B) := by
  obtain ⟨W, col, hW, hE, hH, hL⟩ := h
  refine ⟨fun i => (W i).map (Prod.map ψ ψ), col, fun i => (hW i).map ψ, ?_, ?_, ?_⟩
  · rw [localReg2_stepMS_map]
    exact localReg2_offDiag_map_congr ψ hE
  · intro A' hA'
    let σ : N' → N := fun c' => if h : Int' c' then Classical.choose (hI c' h) else u
    have hσ : ∀ c', Int' c' → Int (σ c') ∧ ψ (σ c') = c' := by
      intro c' hc'
      simp only [σ, hc', ↓reduceDIte]
      exact Classical.choose_spec (hI c' hc')
    have hinj : Set.InjOn σ A' := by
      intro c₁ h₁ c₂ h₂ h
      have := congrArg ψ h
      rw [(hσ c₁ (hA' c₁ h₁)).2, (hσ c₂ (hA' c₂ h₂)).2] at this
      exact this
    have hcard : (A'.image σ).card = A'.card := Finset.card_image_of_injOn hinj
    have := hH (A'.image σ) (by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
      exact (hσ c' (hA' c' hc')).1)
    rw [hcard] at this
    refine this.trans (Finset.card_le_card ?_)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨c, hc, hv⟩ := hi
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
    refine ⟨c', hc', ?_⟩
    have := hv.map ψ
    rwa [(hσ c' (hA' c' hc')).2] at this
  · rintro C' σ ⟨s, hs, hs1, hs2⟩
    obtain ⟨s₀, hs₀, rfl⟩ := Multiset.mem_map.1 hs
    obtain ⟨C, hC, rfl⟩ := Sym2.mem_map.1 hs2
    obtain ⟨i, hi1, hi2⟩ := hL C σ ⟨s₀, hs₀, hs1, hC⟩
    exact ⟨i, hi1, hi2.map ψ⟩

/-- Loops cost nothing: dropping diagonal edges keeps the family. -/
theorem localReg2_Fam.of_add_diag {p : ℕ} {u v : N} {Int : N → Prop} {B D : Multiset (Bool × Sym2 N)}
    (hD : ∀ s ∈ D, s.2.IsDiag) : localReg2_Fam p u v Int (B + D) → localReg2_Fam p u v Int B := by
  rintro ⟨W, col, hW, hE, hH, hL⟩
  refine ⟨W, col, hW, ?_, hH, fun C σ hC => hL C σ (localReg2_present_add_left hC)⟩
  rw [hE, localReg2_offDiag_add, localReg2_offDiag_of_diag hD, add_zero]

/-- Diagonal edges whose colours are already present may be added. -/
theorem localReg2_Fam.add_diag {p : ℕ} {u v : N} {Int : N → Prop} {B D : Multiset (Bool × Sym2 N)}
    (hD : ∀ s ∈ D, s.2.IsDiag) (hcov : ∀ s ∈ D, ∀ C ∈ s.2, localReg2_present B C s.1) :
    localReg2_Fam p u v Int B → localReg2_Fam p u v Int (B + D) := by
  rintro ⟨W, col, hW, hE, hH, hL⟩
  refine ⟨W, col, hW, ?_, hH, ?_⟩
  · rw [hE, localReg2_offDiag_add, localReg2_offDiag_of_diag hD, add_zero]
  · rintro C σ ⟨s, hs, h1, h2⟩
    rcases Multiset.mem_add.1 hs with hs | hs
    · exact hL C σ ⟨s, hs, h1, h2⟩
    · exact hL C σ (h1 ▸ hcov s hs C h2)

/-- The colour flip of a coloured pair. -/
def localReg2_flip (c : Bool) (s : Bool × Sym2 N) : Bool × Sym2 N := (xor s.1 c, s.2)

theorem localReg2_flip_flip (c : Bool) (s : Bool × Sym2 N) : localReg2_flip c (localReg2_flip c s) = s := by
  obtain ⟨σ, z⟩ := s
  cases σ <;> cases c <;> rfl

theorem localReg2_flip_flip_ms (c : Bool) (B : Multiset (Bool × Sym2 N)) :
    (B.map (localReg2_flip c)).map (localReg2_flip c) = B := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id B]
  exact Multiset.map_congr rfl fun s _ => localReg2_flip_flip c s

/-- **A global flip of the colours keeps the family** (the walks flip their colours too). -/
theorem localReg2_Fam.flip (c : Bool) {p : ℕ} {u v : N} {Int : N → Prop} {B : Multiset (Bool × Sym2 N)} :
    localReg2_Fam p u v Int B → localReg2_Fam p u v Int (B.map (localReg2_flip c)) := by
  rintro ⟨W, col, hW, hE, hH, hL⟩
  refine ⟨W, fun i => xor (col i) c, hW, ?_, hH, ?_⟩
  · have h1 : localReg2_stepMS (fun i => xor (col i) c) W = (localReg2_stepMS col W).map (localReg2_flip c) := by
      unfold localReg2_stepMS
      have h := map_sum (Multiset.mapAddMonoidHom (localReg2_flip c))
        (fun i => (localReg_stepEdges (W i)).map fun s => (col i, s)) Finset.univ
      refine Eq.trans ?_ h.symm
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
      rfl
    have h2 : ∀ m : Multiset (Bool × Sym2 N), localReg2_offDiag (m.map (localReg2_flip c)) =
        (localReg2_offDiag m).map (localReg2_flip c) := by
      intro m
      unfold localReg2_offDiag
      rw [Multiset.filter_map]
      rfl
    rw [h1, h2, h2, hE]
  · rintro C σ ⟨s, hs, h1, h2⟩
    obtain ⟨s₀, hs₀, rfl⟩ := Multiset.mem_map.1 hs
    obtain ⟨i, hi1, hi2⟩ := hL C s₀.1 ⟨s₀, hs₀, rfl, h2⟩
    refine ⟨i, ?_, hi2⟩
    simp only [localReg2_flip] at h1 ⊢
    rw [hi1]
    exact h1


/-- A replacement walk through a node `X` of a step `(a, b)` or `(b, a)`; it ends where the step ends and visits `X`. -/
theorem localReg2_exists_through (X : N) {st : N × N} {a b : N} (hs : s(st.1, st.2) = s(a, b)) :
    ∃ ω : List (N × N), localReg_StepWalk st.1 st.2 ω ∧ localReg_stepEdges ω = {s(a, X), s(X, b)} ∧
      (∃ st' ∈ ω, st'.2 = st.2) ∧ ∃ st' ∈ ω, st'.2 = X := by
  rcases Sym2.eq_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨[(a, X), (X, b)], ?_, ?_, ⟨(X, b), by simp, by simp [h2]⟩, ⟨(a, X), by simp, rfl⟩⟩
    · rw [h1, h2]
      exact localReg_StepWalk.cons a X b _ (localReg_StepWalk.cons X b b [] (localReg_StepWalk.nil b))
    · simp only [localReg_stepEdges, List.map_cons, List.map_nil]; rfl
  · refine ⟨[(b, X), (X, a)], ?_, ?_, ⟨(X, a), by simp, by simp [h2]⟩, ⟨(b, X), by simp, rfl⟩⟩
    · rw [h1, h2]
      exact localReg_StepWalk.cons b X a _ (localReg_StepWalk.cons X a a [] (localReg_StepWalk.nil a))
    · simp only [localReg_stepEdges, List.map_cons, List.map_nil]
      rw [Sym2.eq_swap (a := b) (b := X), Sym2.eq_swap (a := X) (b := a)]
      change (s(X, b) ::ₘ s(a, X) ::ₘ (0 : Multiset (Sym2 N))) = s(a, X) ::ₘ s(X, b) ::ₘ 0
      exact Multiset.cons_swap _ _ _

/-- A walk that visits `a` splits at a visit of `a`. -/
theorem localReg2_visits_split {v a : N} : ∀ {u : N} {l : List (N × N)}, localReg_StepWalk u v l →
    localReg_StepWalk.Visits u l a →
    ∃ l₁ l₂ : List (N × N), l = l₁ ++ l₂ ∧ localReg_StepWalk u a l₁ ∧ localReg_StepWalk a v l₂ := by
  intro u l
  induction l generalizing u with
  | nil =>
    intro hw hv
    rcases hv with h | ⟨st, hst, _⟩
    · subst h; exact ⟨[], [], rfl, localReg_StepWalk.nil _, hw⟩
    · simp at hst
  | cons st l ih =>
    intro hw hv
    obtain ⟨a', b'⟩ := st
    obtain ⟨hua, hbv⟩ := hw
    rcases hv with h | ⟨st', hst', hst'a⟩
    · subst h
      exact ⟨[], (a', b') :: l, rfl, localReg_StepWalk.nil _, ⟨hua, hbv⟩⟩
    · simp only [List.mem_cons] at hst'
      rcases hst' with rfl | hst'
      · have hb : b' = a := hst'a
        subst hb
        exact ⟨[(a', b')], l, rfl, ⟨hua, rfl⟩, hbv⟩
      · obtain ⟨l₁, l₂, hl, h1, h2⟩ := ih hbv (Or.inr ⟨st', hst', hst'a⟩)
        exact ⟨(a', b') :: l₁, l₂, by simp [hl], ⟨hua, h1⟩, h2⟩

theorem localReg2_stepMS_split {p : ℕ} (col : Fin p → Bool) (W : Fin p → List (N × N)) (i : Fin p) :
    localReg2_stepMS col W = (localReg_stepEdges (W i)).map (fun s => (col i, s)) +
      ∑ j ∈ Finset.univ \ {i}, (localReg_stepEdges (W j)).map fun s => (col j, s) := by
  unfold localReg2_stepMS
  exact Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) _

theorem localReg2_stepMS_update {p : ℕ} (col : Fin p → Bool) (W : Fin p → List (N × N)) (i : Fin p) (L : List (N × N)) :
    localReg2_stepMS col (Function.update W i L) = (localReg_stepEdges L).map (fun s => (col i, s)) +
      ∑ j ∈ Finset.univ \ {i}, (localReg_stepEdges (W j)).map fun s => (col j, s) := by
  unfold localReg2_stepMS
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have : j ≠ i := by simpa using hj
  rw [Function.update_of_ne this]


/-- **Rerouting through a node** (coloured, exact): one edge `(σ, {a, b})` of the budget is replaced by `(σ, {a, X})`, `(σ, {X, b})`;
the walk that used it passes through `X`; if the edge is a loop (`a = b`), a closed detour through `X` is inserted into a walk of colour
`σ` visiting `a`. -/
theorem localReg2_Fam.thr {p : ℕ} {u v : N} {Int : N → Prop} {R : Multiset (Bool × Sym2 N)} (σ : Bool) (a b X : N) :
    localReg2_Fam p u v Int (R + {(σ, s(a, b))}) → localReg2_Fam p u v Int (R + {(σ, s(a, X)), (σ, s(X, b))}) := by
  rintro ⟨W, col, hW, hE, hH, hL⟩
  have heR : (σ, s(a, b)) ∈ R + {(σ, s(a, b))} := Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self _))
  by_cases hab : a = b
  · subst hab
    obtain ⟨i, hi1, hi2⟩ := hL a σ ⟨(σ, s(a, a)), heR, rfl, Sym2.mem_mk_left a a⟩
    obtain ⟨l₁, l₂, hl, h1, h2⟩ := localReg2_visits_split (hW i) hi2
    set det : List (N × N) := [(a, X), (X, a)] with hdet
    have hdetW : localReg_StepWalk a a det :=
      localReg_StepWalk.cons a X a _ (localReg_StepWalk.cons X a a [] (localReg_StepWalk.nil a))
    set W' : Fin p → List (N × N) := Function.update W i (l₁ ++ det ++ l₂) with hW'
    have hW'i : W' i = l₁ ++ det ++ l₂ := by simp [hW']
    have hW'j : ∀ j, j ≠ i → W' j = W j := fun j hj => by simp [hW', hj]
    have hvis : ∀ j C, localReg_StepWalk.Visits u (W j) C → localReg_StepWalk.Visits u (W' j) C := by
      intro j C hC
      by_cases hj : j = i
      · subst hj
        rw [hW'i]
        rcases hC with hC | ⟨st, hst, hstC⟩
        · exact Or.inl hC
        · right
          rw [hl] at hst
          simp only [List.mem_append] at hst ⊢
          rcases hst with h | h
          · exact ⟨st, Or.inl (Or.inl h), hstC⟩
          · exact ⟨st, Or.inr h, hstC⟩
      · rw [hW'j j hj]; exact hC
    have hX : localReg_StepWalk.Visits u (W' i) X := by
      right
      rw [hW'i]
      exact ⟨(a, X), by simp [hdet], rfl⟩
    have hdetE : localReg_stepEdges det = {s(a, X), s(X, a)} := by
      simp only [hdet, localReg_stepEdges, List.map_cons, List.map_nil]; rfl
    refine ⟨W', col, ?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj; rw [hW'i]; exact (h1.append hdetW).append h2
      · rw [hW'j j hj]; exact hW j
    · have e1 := localReg2_stepMS_split col W i
      have e2 : localReg2_stepMS col W' = _ := localReg2_stepMS_update col W i (l₁ ++ det ++ l₂)
      have e3 : localReg2_stepMS col W' = localReg2_stepMS col W + {(σ, s(a, X)), (σ, s(X, a))} := by
        rw [e2, e1, hl, localReg_stepEdges_append, localReg_stepEdges_append, localReg_stepEdges_append, hdetE, hi1]
        simp only [Multiset.map_add, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
        abel
      rw [e3, localReg2_offDiag_add, hE, localReg2_offDiag_add, localReg2_offDiag_add,
        localReg2_offDiag_of_diag (a := {(σ, s(a, a))}) (by simp [Sym2.mk_isDiag_iff]), add_zero]
    · intro A hA
      refine (hH A hA).trans (Finset.card_le_card ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      obtain ⟨c, hc, hv⟩ := hj
      exact ⟨c, hc, hvis j c hv⟩
    · rintro C σ' ⟨s, hs, h1', h2'⟩
      rcases Multiset.mem_add.1 hs with hs | hs
      · obtain ⟨j, hj1, hj2⟩ := hL C σ' ⟨s, Multiset.mem_add.2 (Or.inl hs), h1', h2'⟩
        exact ⟨j, hj1, hvis j C hj2⟩
      · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · rcases Sym2.mem_iff.1 h2' with rfl | rfl
          · exact ⟨i, by rw [hi1]; exact h1', hvis i _ hi2⟩
          · exact ⟨i, by rw [hi1]; exact h1', hX⟩
        · rcases Sym2.mem_iff.1 h2' with rfl | rfl
          · exact ⟨i, by rw [hi1]; exact h1', hX⟩
          · exact ⟨i, by rw [hi1]; exact h1', hvis i _ hi2⟩
  · have hnd : ¬ (s(a, b) : Sym2 N).IsDiag := by simpa [Sym2.mk_isDiag_iff] using hab
    have hmem : (σ, s(a, b)) ∈ localReg2_stepMS col W := by
      have : (σ, s(a, b)) ∈ localReg2_offDiag (R + {(σ, s(a, b))}) := localReg2_mem_offDiag.2 ⟨heR, hnd⟩
      rw [← hE] at this
      exact (localReg2_mem_offDiag.1 this).1
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hmem
    obtain ⟨s', hs', hs'e⟩ := Multiset.mem_map.1 hi
    have hcol : col i = σ := congrArg Prod.fst hs'e
    have hs'ab : s' = s(a, b) := congrArg Prod.snd hs'e
    obtain ⟨st, hst, hstE⟩ := localReg_mem_stepEdges.1 hs'
    have hst' : s(st.1, st.2) = s(a, b) := hstE.trans hs'ab
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hst
    obtain ⟨ω, hω, hωm, ⟨st', hst'ω, hst'e⟩, ⟨st'', hst''ω, hst''e⟩⟩ := localReg2_exists_through X hst'
    set W' : Fin p → List (N × N) := Function.update W i (A ++ ω ++ B) with hW'
    have hW'i : W' i = A ++ ω ++ B := by simp [hW']
    have hW'j : ∀ j, j ≠ i → W' j = W j := fun j hj => by simp [hW', hj]
    have hAB' := hW i
    rw [hAB] at hAB'
    obtain ⟨x₁, hA, hx₁⟩ := localReg_StepWalk.append_inv hAB'
    obtain ⟨rfl, hB'⟩ := localReg_StepWalk.cons_inv (a := st.1) (b := st.2) (l := B) (by simpa using hx₁)
    have hvis : ∀ j C, localReg_StepWalk.Visits u (W j) C → localReg_StepWalk.Visits u (W' j) C := by
      intro j C hC
      by_cases hj : j = i
      · subst hj
        rw [hW'i]
        rw [hAB] at hC
        rcases hC with hC | ⟨st3, hst3, hst3c⟩
        · exact Or.inl hC
        · right
          simp only [List.mem_append, List.mem_cons] at hst3
          rcases hst3 with hh | hh | hh
          · exact ⟨st3, by simp [hh], hst3c⟩
          · exact ⟨st', by simp [hst'ω], by rw [hst'e, ← hh, hst3c]⟩
          · exact ⟨st3, by simp [hh], hst3c⟩
      · rw [hW'j j hj]; exact hC
    have hX : localReg_StepWalk.Visits u (W' i) X := by
      right
      rw [hW'i]
      exact ⟨st'', by simp [hst''ω], hst''e⟩
    refine ⟨W', col, ?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj; rw [hW'i]; exact (hA.append hω).append hB'
      · rw [hW'j j hj]; exact hW j
    · obtain ⟨S₀, e1, e2⟩ : ∃ S₀ : Multiset (Bool × Sym2 N), localReg2_stepMS col W = S₀ + {(σ, s(a, b))} ∧
          localReg2_stepMS col W' = S₀ + {(σ, s(a, X)), (σ, s(X, b))} := by
        refine ⟨(localReg_stepEdges A).map (fun s => (σ, s)) + (localReg_stepEdges B).map (fun s => (σ, s)) +
          ∑ j ∈ Finset.univ \ {i}, (localReg_stepEdges (W j)).map fun s => (col j, s), ?_, ?_⟩
        · rw [localReg2_stepMS_split col W i, hAB, localReg_stepEdges_append, localReg_stepEdges_cons, hstE, hs'ab, hcol]
          simp only [Multiset.map_add, Multiset.map_cons]
          rw [← Multiset.singleton_add]
          abel
        · rw [hW', localReg2_stepMS_update col W i (A ++ ω ++ B), localReg_stepEdges_append, localReg_stepEdges_append, hωm, hcol]
          simp only [Multiset.map_add, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
          abel
      have e3 : localReg2_offDiag R = localReg2_offDiag S₀ := by
        have h := hE
        rw [e1, localReg2_offDiag_add S₀, localReg2_offDiag_add R,
          localReg2_offDiag_eq_self (a := {(σ, s(a, b))}) (by simpa using hnd)] at h
        exact (add_right_cancel h).symm
      rw [e2, localReg2_offDiag_add S₀, localReg2_offDiag_add R, e3]
    · intro A' hA'
      refine (hH A' hA').trans (Finset.card_le_card ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      obtain ⟨c, hc, hv⟩ := hj
      exact ⟨c, hc, hvis j c hv⟩
    · rintro C σ' ⟨s, hs, h1', h2'⟩
      rcases Multiset.mem_add.1 hs with hs | hs
      · obtain ⟨j, hj1, hj2⟩ := hL C σ' ⟨s, Multiset.mem_add.2 (Or.inl hs), h1', h2'⟩
        exact ⟨j, hj1, hvis j C hj2⟩
      · have hpa : ∀ C, C ∈ (s(a, b) : Sym2 N) → ∃ j, col j = σ ∧ localReg_StepWalk.Visits u (W' j) C := by
          intro C hC
          obtain ⟨j, hj1, hj2⟩ := hL C σ ⟨(σ, s(a, b)), heR, rfl, hC⟩
          exact ⟨j, hj1, hvis j C hj2⟩
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · rcases Sym2.mem_iff.1 h2' with rfl | rfl
          · obtain ⟨j, hj1, hj2⟩ := hpa _ (Sym2.mem_mk_left _ _)
            exact ⟨j, by rw [hj1]; exact h1', hj2⟩
          · exact ⟨i, by rw [hcol]; exact h1', hX⟩
        · rcases Sym2.mem_iff.1 h2' with rfl | rfl
          · exact ⟨i, by rw [hcol]; exact h1', hX⟩
          · obtain ⟨j, hj1, hj2⟩ := hpa _ (Sym2.mem_mk_right _ _)
            exact ⟨j, by rw [hj1]; exact h1', hj2⟩


/-- **Replacement of `Rem` by `New` in the budget `R + ·`** (at the given rest `R`). -/
def localReg2_FamReplAt (R Rem New : Multiset (Bool × Sym2 N)) : Prop :=
  ∀ (p : ℕ) (u v : N) (Int : N → Prop), localReg2_Fam p u v Int (R + Rem) → localReg2_Fam p u v Int (R + New)

/-- The same edges up to loops: `D₁ + A` is replaced by `A + D₂` (`D₁`, `D₂` diagonal; the colours of `D₂` are present in `D₁ + A`). -/
theorem localReg2_Fam.repl_same {p : ℕ} {u v : N} {Int : N → Prop} {R D₁ A D₂ : Multiset (Bool × Sym2 N)}
    (hD₁ : ∀ s ∈ D₁, s.2.IsDiag) (hD₂ : ∀ s ∈ D₂, s.2.IsDiag)
    (hcov : ∀ s ∈ D₂, ∀ C ∈ s.2, localReg2_present (D₁ + A) C s.1)
    (h : localReg2_Fam p u v Int (R + (D₁ + A))) : localReg2_Fam p u v Int (R + (A + D₂)) := by
  have h1 := localReg2_Fam.add_diag hD₂ (fun s hs C hC => localReg2_present_add_right (hcov s hs C hC)) h
  have e : R + (D₁ + A) + D₂ = (R + (A + D₂)) + D₁ := by abel
  rw [e] at h1
  exact localReg2_Fam.of_add_diag hD₁ h1

/-- The derivative replacement: the edge `(σ, {a, b})` is replaced by `(σ, {a, X})`, `(σ, {X, b})`; `D₁` (diagonal) removed, `D₂`
(diagonal, with colours present in the old edges) added. -/
theorem localReg2_Fam.repl_deriv {p : ℕ} {u v : N} {Int : N → Prop} {R D₁ A D₂ : Multiset (Bool × Sym2 N)}
    (σ : Bool) (a b X : N) (hD₁ : ∀ s ∈ D₁, s.2.IsDiag) (hD₂ : ∀ s ∈ D₂, s.2.IsDiag)
    (hcov : ∀ s ∈ D₂, ∀ C ∈ s.2, localReg2_present (D₁ + {(σ, s(a, b))} + A) C s.1)
    (h : localReg2_Fam p u v Int (R + (D₁ + {(σ, s(a, b))} + A))) :
    localReg2_Fam p u v Int (R + ({(σ, s(a, X)), (σ, s(X, b))} + A + D₂)) := by
  have h1 := localReg2_Fam.add_diag hD₂ (fun s hs C hC => localReg2_present_add_right (hcov s hs C hC)) h
  have e : R + (D₁ + {(σ, s(a, b))} + A) + D₂ = (R + A + D₂ + {(σ, s(a, b))}) + D₁ := by abel
  rw [e] at h1
  have h2 := localReg2_Fam.thr (R := R + A + D₂) σ a b X (localReg2_Fam.of_add_diag hD₁ h1)
  have e2 : R + A + D₂ + {(σ, s(a, X)), (σ, s(X, b))} = R + ({(σ, s(a, X)), (σ, s(X, b))} + A + D₂) := by abel
  rwa [e2] at h2

end Walks2

/-! ## 2. The invariant on graphs

`LGraph.localReg2_PathFam Γ p x y`: the coloured family on the molecules of `Γ` with the budget of its solid edges.  Transfer along a vertex map
(`localReg2_pathFam_map`), along the dotted edge partition (`localReg2_pathFam_partition`) and along one expansion term (`localReg2_pathFam_term`). -/

section GraphLevel2

/-- The coloured unordered ends of a solid edge: its colour and the pair of its ends. -/
def SEdge.localReg2_cends {V : Type*} (e : SEdge V) : Bool × Sym2 V := (e.σ, s(e.src, e.dst))

@[simp] theorem SEdge.localReg2_cends_mk {V : Type*} (σ c : Bool) (a b : V) :
    (⟨σ, c, a, b⟩ : SEdge V).localReg2_cends = (σ, s(a, b)) := rfl

theorem SEdge.localReg2_cends_map {V W : Type*} (f : V → W) (e : SEdge V) :
    (SEdge.map f e).localReg2_cends = Prod.map id (Sym2.map f) e.localReg2_cends := rfl

/-- The twist `(c, t)` of a solid edge flips its colour by `c` and keeps its unordered ends. -/
theorem SEdge.localReg2_cends_twist {V : Type*} (c t : Bool) (e : SEdge V) :
    (lwSymmTwistS c t e).localReg2_cends = localReg2_flip c e.localReg2_cends := by
  cases c <;> cases t <;> simp [lwSymmTwistS, SEdge.localReg2_cends, SEdge.conj, SEdge.transpose, localReg2_flip, Sym2.eq_swap]

theorem localReg2_mapMS_comp {V W U : Type*} (f : V → W) (g : W → U) (B : Multiset (Bool × Sym2 V)) :
    localReg2_mapMS g (localReg2_mapMS f B) = localReg2_mapMS (fun v => g (f v)) B := by
  unfold localReg2_mapMS
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun s _ => ?_
  obtain ⟨σ, z⟩ := s
  simp [Sym2.map_map]

theorem localReg2_mapMS_flip {V W : Type*} (f : V → W) (c : Bool) (B : Multiset (Bool × Sym2 V)) :
    localReg2_mapMS f (B.map (localReg2_flip c)) = (localReg2_mapMS f B).map (localReg2_flip c) := by
  unfold localReg2_mapMS
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun s _ => ?_
  obtain ⟨σ, z⟩ := s
  rfl

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The coloured unordered ends of the solid edges of a graph (weights included), with multiplicity. -/
def LGraph.localReg2_cendsMS (Γ : LGraph E I) : Multiset (Bool × Sym2 (E ⊕ I)) :=
  ((Γ.solid.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I))) : Multiset (Bool × Sym2 (E ⊕ I)))

/-- The solid edges of a graph as coloured pairs of molecules (the edges inside a molecule give diagonal pairs). -/
def LGraph.localReg2_edgeMS (Γ : LGraph E I) : Multiset (Bool × Sym2 Γ.Mol) :=
  localReg2_mapMS Γ.molOf Γ.localReg2_cendsMS

/-- **The coloured path invariant** at the vertices `x`, `y`: a coloured exact family of `p` walks from the molecule of `x` to that
of `y` in the molecular multigraph, with the Hall condition on the internal molecules. -/
def LGraph.localReg2_PathFam (Γ : LGraph E I) (p : ℕ) (x y : E ⊕ I) : Prop :=
  localReg2_Fam p (Γ.molOf x) (Γ.molOf y) (fun c => ¬ Γ.IsExtMol c) Γ.localReg2_edgeMS

/-- **The invariant along a vertex map** (as `localReg_pathFam_map`). -/
theorem LGraph.localReg2_pathFam_map {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
    [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]
    (Γ : LGraph E₁ I₁) (Γ' : LGraph E₂ I₂) (φ : E₁ ⊕ I₁ → E₂ ⊕ I₂)
    (hl : ∀ a : E₁, ∃ a' : E₂, φ (Sum.inl a) = Sum.inl a')
    (hφ : ∀ v', ∃ v, Γ'.molGraph.Reachable v' (φ v))
    (hadj : ∀ u v, Γ.adj u v = true → Γ'.molGraph.Reachable (φ u) (φ v))
    {p : ℕ} {x y : E₁ ⊕ I₁} (h : Γ.localReg2_PathFam p x y) :
    localReg2_Fam p (Γ'.molOf (φ x)) (Γ'.molOf (φ y)) (fun c => ¬ Γ'.IsExtMol c)
      (localReg2_mapMS (fun v => Γ'.molOf (φ v)) Γ.localReg2_cendsMS) := by
  obtain ⟨ψ, hψ⟩ := Γ.localReg_exists_molMap Γ' φ hadj
  have hsurj : Function.Surjective ψ := by
    intro c'
    induction c' using SimpleGraph.ConnectedComponent.ind with | h v' => ?_
    obtain ⟨v, hv⟩ := hφ v'
    exact ⟨Γ.molOf v, by rw [hψ]; exact (SimpleGraph.ConnectedComponent.eq.2 hv).symm⟩
  have hI : ∀ c' : Γ'.Mol, ¬ Γ'.IsExtMol c' → ∃ c : Γ.Mol, ¬ Γ.IsExtMol c ∧ ψ c = c' := by
    intro c' hc'
    refine ⟨Function.surjInv hsurj c', ?_, Function.surjInv_eq hsurj c'⟩
    rintro ⟨a, ha⟩
    apply hc'
    obtain ⟨a', ha'⟩ := hl a
    refine ⟨a', ?_⟩
    have h1 : ψ (Γ.molOf (Sum.inl a)) = c' := by rw [ha]; exact Function.surjInv_eq hsurj c'
    rw [hψ, ha'] at h1
    exact h1
  have := localReg2_Fam.map ψ hI h
  have hb : localReg2_mapMS ψ Γ.localReg2_edgeMS = localReg2_mapMS (fun v => Γ'.molOf (φ v)) Γ.localReg2_cendsMS := by
    unfold LGraph.localReg2_edgeMS
    rw [localReg2_mapMS_comp]
    unfold localReg2_mapMS
    refine Multiset.map_congr rfl fun s _ => ?_
    obtain ⟨σ, z⟩ := s
    induction z using Sym2.ind with
    | h a b => simp [hψ]
  rw [hb, hψ, hψ] at this
  exact this

/-- The weight split of a list of solid edges changes the coloured ends by loops only (the dropped weights). -/
theorem localReg2_lvl1Split_cends {V : Type*} {es es' : List (SEdge V)} {d : ℕ} (h : lvl1Split es es' d) :
    ∃ D : Multiset (Bool × Sym2 V), (∀ s ∈ D, s.2.IsDiag) ∧
      ((es.map SEdge.localReg2_cends : List (Bool × Sym2 V)) : Multiset (Bool × Sym2 V)) =
        ((es'.map SEdge.localReg2_cends : List (Bool × Sym2 V)) : Multiset (Bool × Sym2 V)) + D := by
  induction h with
  | nil => exact ⟨0, by simp, by simp⟩
  | keep e hne _ ih =>
    obtain ⟨D, hD, hE⟩ := ih
    refine ⟨D, hD, ?_⟩
    simp only [List.map_cons, ← Multiset.cons_coe, hE, Multiset.cons_add]
  | circ e h1 h2 _ ih =>
    obtain ⟨D, hD, hE⟩ := ih
    refine ⟨D, hD, ?_⟩
    simp only [List.map_cons, ← Multiset.cons_coe, hE, Multiset.cons_add]
    rfl
  | drop e h1 h2 _ ih =>
    obtain ⟨D, hD, hE⟩ := ih
    refine ⟨e.localReg2_cends ::ₘ D, ?_, ?_⟩
    · intro s hs
      rcases Multiset.mem_cons.1 hs with rfl | hs
      · simp [SEdge.localReg2_cends, h1]
      · exact hD s hs
    · simp only [List.map_cons, ← Multiset.cons_coe, hE]
      rw [Multiset.add_cons]


/-- **The dotted edge partition keeps the coloured invariant** (as `localReg_pathFam_partition`). -/
theorem LGraph.localReg2_pathFam_partition (m : ℂ) (Δ : LGraph E I) (Q : PGraph E) (hQ : Q ∈ Δ.partition m) {p : ℕ} {a b : E}
    (h : Δ.localReg2_PathFam p (Sum.inl a) (Sum.inl b)) :
    Q.g.localReg2_PathFam p (Sum.inl (Q.ext a)) (Sum.inl (Q.ext b)) := by
  obtain ⟨vm, d, hsurj, hl, hsep, hdoteq, hwav, hsplit⟩ := lvl1_part_struct m Δ Q hQ
  have hadj : ∀ u v, Δ.adj u v = true → Q.g.molGraph.Reachable (vm u) (vm v) := by
    intro u v h
    by_cases huv : vm u = vm v
    · rw [huv]
    · refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨huv, ?_⟩)
      simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h ⊢
      rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
      · left
        refine ⟨WEdge.map vm e, ?_, ?_⟩
        · rw [hwav]; exact List.mem_map_of_mem he
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; simp [WEdge.map, h1, h2]
          · right; simp [WEdge.map, h1, h2]
      · exfalso
        apply huv
        have := hdoteq e he h1
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact this
        · rw [← h1, ← h2]; exact this.symm
  have hmap := Δ.localReg2_pathFam_map Q.g vm (fun a => ⟨_, hl a⟩) (fun v' => by
    obtain ⟨v, hv⟩ := hsurj v'
    exact ⟨v, by rw [hv]⟩) hadj h
  rw [hl a, hl b] at hmap
  obtain ⟨D, hD, hE⟩ := localReg2_lvl1Split_cends hsplit
  have hbud : localReg2_mapMS (fun v => Q.g.molOf (vm v)) Δ.localReg2_cendsMS =
      Q.g.localReg2_edgeMS + localReg2_mapMS Q.g.molOf D := by
    have e1 : localReg2_mapMS vm Δ.localReg2_cendsMS =
        ((Δ.solid.map (SEdge.map vm)).map SEdge.localReg2_cends : List (Bool × Sym2 (Q.E' ⊕ Q.I'))) := by
      unfold LGraph.localReg2_cendsMS localReg2_mapMS
      rw [Multiset.map_coe, List.map_map, List.map_map]
      rfl
    have e2 : localReg2_mapMS (fun v => Q.g.molOf (vm v)) Δ.localReg2_cendsMS =
        localReg2_mapMS Q.g.molOf (localReg2_mapMS vm Δ.localReg2_cendsMS) := by
      rw [localReg2_mapMS_comp]
    rw [e2, e1, hE, localReg2_mapMS_add]
    rfl
  rw [hbud] at hmap
  refine localReg2_Fam.of_add_diag (D := localReg2_mapMS Q.g.molOf D) ?_ hmap
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
  have := hD _ ht
  exact (Sym2.IsDiag.map this)

/-- **Stage 1 of a step** (as `localReg_pathFam_stage1`, with the colours flipped by `c`): the invariant passes from `Γ` to a term `Δ`
that contains the edges of `Γ` on the vertices `emb u`, up to a replacement of `Rem` by `New` at the rest `R`. -/
theorem LGraph.localReg2_pathFam_stage1 {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (Δ : LGraph E I'')
    (emb : E ⊕ I → E ⊕ I'') (hinl : ∀ a, emb (Sum.inl a) = Sum.inl a)
    (hadj : ∀ u v, Γ.adj u v = true → Δ.molGraph.Reachable (emb u) (emb v))
    (hreach : ∀ w, ∃ u, Δ.molGraph.Reachable w (emb u)) (c : Bool)
    {R Rem New : Multiset (Bool × Sym2 Δ.Mol)}
    (hΓ : localReg2_mapMS (fun v => Δ.molOf (emb v)) Γ.localReg2_cendsMS = (R + Rem).map (localReg2_flip c))
    (hΔ : Δ.localReg2_edgeMS = (R + New).map (localReg2_flip c)) (hrepl : localReg2_FamReplAt R Rem New)
    {p : ℕ} {a b : E} (h : Γ.localReg2_PathFam p (Sum.inl a) (Sum.inl b)) :
    Δ.localReg2_PathFam p (Sum.inl a) (Sum.inl b) := by
  have hm := Γ.localReg2_pathFam_map Δ emb (fun a => ⟨a, hinl a⟩) hreach hadj h
  rw [hΓ, hinl, hinl] at hm
  have hm' := localReg2_Fam.flip c hm
  rw [localReg2_flip_flip_ms] at hm'
  have h3 := localReg2_Fam.flip c (hrepl p _ _ _ hm')
  rw [← hΔ] at h3
  exact h3

/-- The twist `(c, t)` does not change the molecules. -/
theorem localReg2_lwSymmTwistG_molGraph (c t : Bool) (Γ : LGraph E I) : (lwSymmTwistG c t Γ).molGraph = Γ.molGraph :=
  localReg_lwSymmTwistG_molGraph c t Γ

/-- A permutation of the solid edges does not change the multiset of the coloured ends. -/
theorem LGraph.localReg2_cendsMS_of_perm {Γ : LGraph E I} {L : List (SEdge (E ⊕ I))} (h : Γ.solid.Perm L) :
    Γ.localReg2_cendsMS = ((L.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I))) : Multiset (Bool × Sym2 (E ⊕ I))) :=
  Multiset.coe_eq_coe.2 (h.map _)

/-- The coloured ends of a list of solid edges twisted by `(c, t)`. -/
theorem localReg2_cends_list_twist {V : Type*} (c t : Bool) (l : List (SEdge V)) :
    (((l.map (lwSymmTwistS c t)).map SEdge.localReg2_cends : List (Bool × Sym2 V)) : Multiset (Bool × Sym2 V)) =
      (((l.map SEdge.localReg2_cends : List (Bool × Sym2 V)) : Multiset (Bool × Sym2 V))).map (localReg2_flip c) := by
  rw [Multiset.map_coe, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun e _ => SEdge.localReg2_cends_twist c t e

/-- The coloured ends of the solid edges of a twisted `owxExt` term. -/
theorem localReg2_cendsMS_twistOwx {I'' : Type} [Fintype I''] [DecidableEq I''] (c t : Bool) (G : LGraph E I)
    (emb : E ⊕ I → E ⊕ I'') (cc : ℂ) (N : List (SEdge (E ⊕ I''))) (W : List (WEdge (E ⊕ I''))) :
    (lwSymmTwistG c t (G.owxExt emb cc N W)).localReg2_cendsMS =
      (localReg2_mapMS emb G.localReg2_cendsMS +
        ((N.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I''))) : Multiset (Bool × Sym2 (E ⊕ I'')))).map (localReg2_flip c) := by
  unfold LGraph.localReg2_cendsMS
  rw [lvl1_twist_owxExt_solid, List.map_append, ← Multiset.coe_add, localReg2_cends_list_twist, Multiset.map_add]
  congr 1
  unfold localReg2_mapMS
  rw [Multiset.map_coe, Multiset.map_coe, List.map_map, List.map_map, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply]
  rw [SEdge.localReg2_cends_map, SEdge.localReg2_cends_twist]
  obtain ⟨σ, z⟩ := e.localReg2_cends
  rfl


/-- **A term of the three expansions, as a packed graph step** (as `localReg_pathFam_term`; the colours are those of the twisted frame:
`Γ`'s coloured ends are those of `Rm + G` flipped by `c`): the invariant passes from `Γ` to `Δ = (G.owxExt emb cc N W)` twisted by `(c, t)`
provided the replacement of (the images of) `Rm` by the new edges `N` holds at the rest `G` for every map `μ` constant on the molecules. -/
theorem localReg2_pathFam_term {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ G : LGraph E I) (c t : Bool)
    (emb : E ⊕ I → E ⊕ I'') (cc : ℂ) (N : List (SEdge (E ⊕ I''))) (W : List (WEdge (E ⊕ I'')))
    (hG : G.adj = Γ.adj) (hinl : ∀ a, emb (Sum.inl a) = Sum.inl a)
    (hreach : ∀ w, ∃ u, (G.owxExt emb cc N W).molGraph.Reachable w (emb u))
    (Rm : Multiset (Bool × Sym2 (E ⊕ I)))
    (hΓ : Γ.localReg2_cendsMS = (Rm + G.localReg2_cendsMS).map (localReg2_flip c))
    (hrepl : ∀ (N' : Type) (μ : E ⊕ I'' → N'),
      (∀ u v, (G.owxExt emb cc N W).molGraph.Reachable u v → μ u = μ v) →
        localReg2_FamReplAt (localReg2_mapMS (fun v => μ (emb v)) G.localReg2_cendsMS)
          (localReg2_mapMS μ (localReg2_mapMS emb Rm))
          (localReg2_mapMS μ ((N.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I''))) : Multiset (Bool × Sym2 (E ⊕ I'')))))
    {p : ℕ} {a b : E} (h : Γ.localReg2_PathFam p (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (G.owxExt emb cc N W)).localReg2_PathFam p (Sum.inl a) (Sum.inl b) := by
  set Δ := lwSymmTwistG c t (G.owxExt emb cc N W) with hΔ
  have hmol : Δ.molGraph = (G.owxExt emb cc N W).molGraph := localReg2_lwSymmTwistG_molGraph c t _
  have hμ : ∀ u v, (G.owxExt emb cc N W).molGraph.Reachable u v → Δ.molOf u = Δ.molOf v :=
    fun u v huv => SimpleGraph.ConnectedComponent.eq.2 (by rw [hmol]; exact huv)
  refine LGraph.localReg2_pathFam_stage1 Γ Δ emb hinl ?_ (fun w => ?_) c
    (R := localReg2_mapMS (fun v => Δ.molOf (emb v)) G.localReg2_cendsMS)
    (Rem := localReg2_mapMS (fun v => Δ.molOf (emb v)) Rm)
    (New := localReg2_mapMS Δ.molOf ((N.map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I''))) : Multiset (Bool × Sym2 (E ⊕ I''))))
    ?_ ?_ ?_ h
  · intro u v huv
    rw [hmol]
    have : (G.owxExt emb cc N W).adj (emb u) (emb v) = true := by
      refine oe2x_adj_owxExt G emb cc N W u v ?_
      rw [congrFun (congrFun hG u) v]; exact huv
    by_cases hne : emb u = emb v
    · rw [hne]
    · exact SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨hne, this⟩)
  · obtain ⟨u, hu⟩ := hreach w
    exact ⟨u, by rw [hmol]; exact hu⟩
  · rw [hΓ, localReg2_mapMS_flip, ← localReg2_mapMS_add, add_comm]
  · have e0 := localReg2_cendsMS_twistOwx c t G emb cc N W
    unfold LGraph.localReg2_edgeMS
    rw [e0, localReg2_mapMS_flip, localReg2_mapMS_add, localReg2_mapMS_comp]
  · have := hrepl Δ.Mol Δ.molOf hμ
    rwa [localReg2_mapMS_comp] at this

end GraphLevel2

/-! ## 3. The terms of the three expansions

One lemma for each output term of `(Owx)`, `(Oe1x)`, `(Oe2x)` (the twisted `owxExt` terms of `Graph/LWSymm.lean`): the edges removed and the edges added,
read in the molecules (the new vertices lie in the molecule of `x`), and the replacement of the former by the latter (`localReg2_VRepl`). -/

section GraphLevel2

/-- `localReg2_FamReplAt` read through a map `μ` of the vertices to the nodes, at every rest. -/
def localReg2_VRepl {V N' : Type*} (μ : V → N') (A B : Multiset (Bool × Sym2 V)) : Prop :=
  ∀ R : Multiset (Bool × Sym2 N'), localReg2_FamReplAt R (localReg2_mapMS μ A) (localReg2_mapMS μ B)

/-- The two edges of the derivative `owxDE a w e` of an edge `e`, read in nodes with `μ a = μ w`, are `(σ, {μ e.src, μ w})`,
`(σ, {μ w, μ e.dst})`, `σ` the colour of `e`. -/
theorem localReg2_owxDE_cends_mol {V N' : Type*} (μ : V → N') (a w : V) (hμ : μ a = μ w) (e : SEdge V) :
    localReg2_mapMS μ {(owxDE a w e).1.localReg2_cends, (owxDE a w e).2.localReg2_cends} =
      {(e.σ, s(μ e.src, μ w)), (e.σ, s(μ w, μ e.dst))} := by
  unfold owxDE localReg2_mapMS
  split_ifs with h
  · simp [SEdge.localReg2_cends, hμ, h]
  · have h' : e.σ = false := by simpa using h
    simp [SEdge.localReg2_cends, hμ, h']

/-- **The derivative replacement** (`owxDE`): an edge `e` is replaced by the two edges of its derivative at `(a, w)` (`a`, `w` in one node),
of the colour of `e`; `D₁` diagonal edges removed, `D₂` diagonal edges added (their colours present among the old edges), the edges `A`
kept (as `A'`, equal in the nodes). -/
theorem localReg2_VRepl.deriv {V N' : Type*} (μ : V → N') (a w : V) (hμ : μ a = μ w) (e : SEdge V) {Rm New : Multiset (Bool × Sym2 V)}
    (D₁ A A' D₂ : Multiset (Bool × Sym2 V)) (hD₁ : ∀ s ∈ D₁, (Sym2.map μ s.2).IsDiag) (hD₂ : ∀ s ∈ D₂, (Sym2.map μ s.2).IsDiag)
    (hcov : ∀ s ∈ D₂, ∀ C ∈ Sym2.map μ s.2, ∃ s' ∈ D₁ + {e.localReg2_cends} + A, s'.1 = s.1 ∧ C ∈ Sym2.map μ s'.2)
    (hAA : localReg2_mapMS μ A = localReg2_mapMS μ A') (hRm : Rm = D₁ + {e.localReg2_cends} + A)
    (hNew : New = {(owxDE a w e).1.localReg2_cends, (owxDE a w e).2.localReg2_cends} + A' + D₂) :
    localReg2_VRepl μ Rm New := by
  subst hRm hNew
  intro R p u v Int h
  have hd := localReg2_owxDE_cends_mol μ a w hμ e
  simp only [localReg2_mapMS_add] at h ⊢
  rw [hd, ← hAA]
  have he : localReg2_mapMS μ {e.localReg2_cends} = {(e.σ, s(μ e.src, μ e.dst))} := rfl
  rw [he] at h
  refine localReg2_Fam.repl_deriv (R := R) (D₁ := localReg2_mapMS μ D₁) (A := localReg2_mapMS μ A) (D₂ := localReg2_mapMS μ D₂) e.σ (μ e.src) (μ e.dst) (μ w) ?_ ?_ ?_ ?_
  · rintro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    exact hD₁ t ht
  · rintro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    exact hD₂ t ht
  · rintro s hs C hC
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    obtain ⟨s', hs', h1, h2⟩ := hcov t ht C hC
    refine ⟨Prod.map id (Sym2.map μ) s', ?_, h1, h2⟩
    have : Prod.map id (Sym2.map μ) s' ∈ localReg2_mapMS μ (D₁ + {e.localReg2_cends} + A) := Multiset.mem_map_of_mem _ hs'
    simpa only [localReg2_mapMS_add, he] using this
  · exact h

/-- **The same edges up to loops and nodes**: `Rm = D₁ + A` (`D₁` diagonal), `New = A' + D₂` (`D₂` diagonal, colours present among the old edges),
`A'` the edges `A` read in the nodes. -/
theorem localReg2_VRepl.same {V N' : Type*} (μ : V → N') {Rm New : Multiset (Bool × Sym2 V)} (D₁ A A' D₂ : Multiset (Bool × Sym2 V))
    (hD₁ : ∀ s ∈ D₁, (Sym2.map μ s.2).IsDiag) (hD₂ : ∀ s ∈ D₂, (Sym2.map μ s.2).IsDiag)
    (hcov : ∀ s ∈ D₂, ∀ C ∈ Sym2.map μ s.2, ∃ s' ∈ D₁ + A, s'.1 = s.1 ∧ C ∈ Sym2.map μ s'.2)
    (hAA : localReg2_mapMS μ A = localReg2_mapMS μ A') (hRm : Rm = D₁ + A) (hNew : New = A' + D₂) :
    localReg2_VRepl μ Rm New := by
  subst hRm hNew
  intro R p u v Int h
  simp only [localReg2_mapMS_add] at h ⊢
  rw [← hAA]
  refine localReg2_Fam.repl_same (R := R) (D₁ := localReg2_mapMS μ D₁) (A := localReg2_mapMS μ A) (D₂ := localReg2_mapMS μ D₂) ?_ ?_ ?_ h
  · rintro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    exact hD₁ t ht
  · rintro s hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    exact hD₂ t ht
  · rintro s hs C hC
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    obtain ⟨s', hs', h1, h2⟩ := hcov t ht C hC
    refine ⟨Prod.map id (Sym2.map μ) s', ?_, h1, h2⟩
    have : Prod.map id (Sym2.map μ) s' ∈ localReg2_mapMS μ (D₁ + A) := Multiset.mem_map_of_mem _ hs'
    simpa only [localReg2_mapMS_add] using this


variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

local macro "localReg2_simp0" : tactic => `(tactic| simp only [SEdge.localReg2_cends_mk, SEdge.localReg2_cends_map, Prod.map_apply, Sym2.map_mk, lwSymmTwistP, localReg2_mapMS, List.map_cons, List.map_nil, Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq])

local macro "localReg2_msnorm" : tactic => `(tactic| (localReg2_simp0; try abel))

/-- A diagonal coloured pair is covered by any pair of the same colour whose nodes contain its node. -/
theorem localReg2_cov_of_forall {V N' : Type*} (μ : V → N') {M D₂ : Multiset (Bool × Sym2 V)}
    (h : ∀ s ∈ D₂, ∃ s' ∈ M, s'.1 = s.1 ∧ ∀ C ∈ Sym2.map μ s.2, C ∈ Sym2.map μ s'.2) :
    ∀ s ∈ D₂, ∀ C ∈ Sym2.map μ s.2, ∃ s' ∈ M, s'.1 = s.1 ∧ C ∈ Sym2.map μ s'.2 := by
  intro s hs C hC
  obtain ⟨s', hs', h1, h2⟩ := h s hs
  exact ⟨s', hs', h1, h2 C hC⟩


/-- `Γ`'s coloured ends in the frame of one selected edge: the twisted `p.1` and the twisted rest, flipped by `c`. -/
theorem localReg2_hΓ_one (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (c t : Bool) :
    Γ.localReg2_cendsMS = (((lwSymmTwistS c t p.1).localReg2_cends ::ₘ 0) +
      (((p.2.map (lwSymmTwistS c t)).map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I))) : Multiset (Bool × Sym2 (E ⊕ I)))).map
        (localReg2_flip c) := by
  rw [LGraph.localReg2_cendsMS_of_perm (lwSplit_perm Γ.solid p hp), localReg2_cends_list_twist]
  simp only [List.map_cons, ← Multiset.cons_coe, SEdge.localReg2_cends_twist, localReg2_flip_flip, Multiset.cons_add, Multiset.zero_add,
    Multiset.map_add, Multiset.map_cons, Multiset.map_zero, localReg2_flip_flip_ms]

/-- the same for two selected edges -/
theorem localReg2_hΓ_two (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (c t : Bool) :
    Γ.localReg2_cendsMS = (((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) +
      (((q.2.map (lwSymmTwistS c t)).map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I))) : Multiset (Bool × Sym2 (E ⊕ I)))).map
        (localReg2_flip c) := by
  have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
  rw [LGraph.localReg2_cendsMS_of_perm h3, localReg2_cends_list_twist]
  simp only [List.map_cons, ← Multiset.cons_coe, SEdge.localReg2_cends_twist, localReg2_flip_flip, Multiset.cons_add, Multiset.zero_add,
    Multiset.map_add, Multiset.map_cons, Multiset.map_zero, localReg2_flip_flip_ms]

/-- the same for three selected edges -/
theorem localReg2_hΓ_three (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) (c t : Bool) :
    Γ.localReg2_cendsMS = (((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ
        (lwSymmTwistS c t q'.1).localReg2_cends ::ₘ 0) +
      (((q'.2.map (lwSymmTwistS c t)).map SEdge.localReg2_cends : List (Bool × Sym2 (E ⊕ I))) : Multiset (Bool × Sym2 (E ⊕ I)))).map
        (localReg2_flip c) := by
  have h3 : Γ.solid.Perm (p.1 :: q.1 :: q'.1 :: q'.2) :=
    (localReg_lwSplit_perm2 Γ.solid p hp q hq).trans (((lwSplit_perm q.2 q' hq').cons q.1).cons p.1)
  rw [LGraph.localReg2_cendsMS_of_perm (localReg_lwSplit_perm3 Γ.solid p hp q hq q' hq'), localReg2_cends_list_twist]
  simp only [List.map_cons, ← Multiset.cons_coe, SEdge.localReg2_cends_twist, localReg2_flip_flip, Multiset.cons_add, Multiset.zero_add,
    Multiset.map_add, Multiset.map_cons, Multiset.map_zero, localReg2_flip_flip_ms]

/-- The frame of a selected edge has the coloured ends of the graph, flipped by `c`. -/
theorem localReg2_frame_cendsMS (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) :
    (lwSymmFrame c t Γ p).localReg2_cendsMS = Γ.localReg2_cendsMS.map (localReg2_flip c) := by
  rw [LGraph.localReg2_cendsMS_of_perm (lwSplit_perm Γ.solid p hp)]
  unfold LGraph.localReg2_cendsMS
  rw [lwSymmFrame_solid]
  simp only [lwSymmFrameP, List.map_cons, ← Multiset.cons_coe, Multiset.map_cons, SEdge.localReg2_cends_twist, localReg2_cends_list_twist]
  rfl

/-- The frame of two selected edges has the coloured ends of the graph, flipped by `c`. -/
theorem localReg2_frame2_cendsMS (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    (lwSymmFrame2 c t Γ p q).localReg2_cendsMS = Γ.localReg2_cendsMS.map (localReg2_flip c) := by
  have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
  rw [LGraph.localReg2_cendsMS_of_perm h3]
  unfold LGraph.localReg2_cendsMS
  rw [lwSymmFrame2_solid]
  simp only [lwSymmFrame2P, List.map_cons, ← Multiset.cons_coe, SEdge.localReg2_cends_twist, localReg2_cends_list_twist]
  rfl

/-- The twisted graph has the coloured ends of the graph, flipped by `c`. -/
theorem localReg2_twistG_cendsMS (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).localReg2_cendsMS = Γ.localReg2_cendsMS.map (localReg2_flip c) := by
  unfold LGraph.localReg2_cendsMS
  rw [lwSymmTwistG_solid, localReg2_cends_list_twist]

/-- Adding a loop of a colour that is present at its node. -/
theorem localReg2_FamReplAt.add_loop {N' : Type*} {R : Multiset (Bool × Sym2 N')} {σ : Bool} {X z : N'}
    (h : (σ, s(X, z)) ∈ R) : localReg2_FamReplAt R 0 {(σ, s(X, X))} := by
  intro p u v Int hF
  rw [add_zero] at hF
  refine localReg2_Fam.add_diag (D := {(σ, s(X, X))}) (by simp [Sym2.mk_isDiag_iff]) ?_ hF
  intro s hs C hC
  simp only [Multiset.mem_singleton] at hs
  subst hs
  simp only [Sym2.mem_iff, or_self] at hC
  subst hC
  exact ⟨(σ, s(C, z)), h, rfl, Sym2.mem_mk_left _ _⟩


/-- `(Owx)` term 3 for the solid edge `q.1 = (a, b)` of `f`: the weight `p.1` is dropped and `q.1` is replaced by the two edges of its
derivative (of the colour of `q.1`), a walk `M(a) → M(x) → M(b)`; the new blue edge `G_{αx}` lies inside `M(x)`. -/
theorem localReg2_pathFam_owxT3 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOwxT3 c t m Γ x q).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT3 owxET3
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 1 x w, lwSymmExt_reach1 _ x _ _ _ false true (by simp) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 x) :=
      hμ _ _ (lwSymmExt_reach1 _ x _ _ _ false true (by simp) (Sum.inr (Sum.inr 0)))
    refine localReg2_VRepl.deriv μ (Sum.inr (Sum.inr 0)) (owxEmb 1 x) hα (SEdge.map (owxEmb 1) (lwSymmTwistS c t q.1))
      {(true, s(owxEmb 1 x, owxEmb 1 x))} 0 0 {(true, s(Sum.inr (Sum.inr 0), owxEmb 1 x))} (by simp) ?_ ?_ rfl ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff, hα]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(true, s(owxEmb 1 x, owxEmb 1 x)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff, hα] at hC ⊢
      tauto
    · rw [hx]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Owx)` term 1 (`m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f`): the frame is kept, the leaf `α` joins the molecule of `x` and carries a blue loop (the
colour of the weight `p.1`, which is kept); no solid edge of `Γ` is removed. -/
theorem localReg2_pathFam_owxT1 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOwxT1 c t m Γ x).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT1 owxET1
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ 0 ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 1 x w, lwSymmExt_reach1 _ x _ _ _ false true (by simp) w⟩
  · rw [zero_add, localReg2_twistG_cendsMS, localReg2_flip_flip_ms]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 x) :=
      hμ _ _ (lwSymmExt_reach1 _ x _ _ _ false true (by simp) (Sum.inr (Sum.inr 0)))
    have hmem : (true, s(μ (owxEmb 1 x), μ (owxEmb 1 x))) ∈
        localReg2_mapMS (fun v => μ (owxEmb 1 v)) (lwSymmTwistG c t Γ).localReg2_cendsMS := by
      have h1 : (lwSymmTwistS c t p.1).localReg2_cends ∈ (lwSymmTwistG c t Γ).localReg2_cendsMS := by
        unfold LGraph.localReg2_cendsMS
        rw [lwSymmTwistG_solid, Multiset.mem_coe]
        exact List.mem_map_of_mem (List.mem_map_of_mem (lvl1_mem_split_fst _ p hp))
      rw [hx] at h1
      exact Multiset.mem_map_of_mem (Prod.map id (Sym2.map fun v => μ (owxEmb 1 v))) h1
    have := localReg2_FamReplAt.add_loop hmem
    simpa [localReg2_mapMS, hα] using this


/-- `(Owx)` term 2: the weight `p.1` (a loop inside the molecule of `x`) is dropped, the blue loops at the path `x ~ α ~ β` are added. -/
theorem localReg2_pathFam_owxT2 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOwxT2 c t m Γ p x).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT2 owxET2
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 2 x w, lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) w⟩
  · exact localReg2_hΓ_one Γ p hp c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 2 x) :=
      hμ _ _ (lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (owxEmb 2 x) :=
      hμ _ _ (lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg2_VRepl.same μ {(true, s(owxEmb 2 x, owxEmb 2 x))} 0 0
      {(true, s(Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0))), (true, s(Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)))}
      (by simp) ?_ ?_ rfl ?_ ?_ _
    · rintro s hs
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> simp [Sym2.mk_isDiag_iff]
    · refine localReg2_cov_of_forall μ ?_
      rintro s hs
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · refine ⟨(true, s(owxEmb 2 x, owxEmb 2 x)), by simp, rfl, ?_⟩
        intro C hC
        simp only [Sym2.map_mk, Sym2.mem_iff, hα] at hC ⊢
        tauto
      · refine ⟨(true, s(owxEmb 2 x, owxEmb 2 x)), by simp, rfl, ?_⟩
        intro C hC
        simp only [Sym2.map_mk, Sym2.mem_iff, hβ] at hC ⊢
        tauto
    · rw [hx]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Owx)` term 4 for `q.1 = (a, b)`: as term 3, with the path `x ~ α ~ β` and the derivative at `(β, α)`. -/
theorem localReg2_pathFam_owxT4 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOwxT4 c t m Γ x q).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT4 owxET4
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 2 x w, lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 2 x) :=
      hμ _ _ (lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (owxEmb 2 x) :=
      hμ _ _ (lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg2_VRepl.deriv μ (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (hβ.trans hα.symm)
      (SEdge.map (owxEmb 2) (lwSymmTwistS c t q.1)) {(true, s(owxEmb 2 x, owxEmb 2 x))} 0 0
      {(true, s(Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0)))} (by simp) ?_ ?_ rfl ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff, hα, hβ]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(true, s(owxEmb 2 x, owxEmb 2 x)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff, hα, hβ] at hC ⊢
      tauto
    · rw [hx]; localReg2_msnorm
    · localReg2_msnorm

/-- The frame of a selected edge has the molecules (the adjacency) of the graph. -/
theorem localReg2_lwSymmFrame_adj (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).adj = Γ.adj := localReg_lwSymmFrame_adj c t Γ p

/-- The twisted selected edge is an edge of its frame (the circle is not part of the coloured ends). -/
theorem localReg2_mem_frame (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmTwistS c t p.1).localReg2_cends ∈ (lwSymmFrame c t Γ p).localReg2_cendsMS := by
  unfold LGraph.localReg2_cendsMS
  rw [lwSymmFrame_solid, Multiset.mem_coe]
  simp only [lwSymmFrameP, List.map_cons, List.mem_cons, lwSymmTwistS_with_circ]
  left
  rfl

/-- The twisted first selected edge is an edge of the frame of two selected edges. -/
theorem localReg2_mem_frame2 (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmTwistS c t p.1).localReg2_cends ∈ (lwSymmFrame2 c t Γ p q).localReg2_cendsMS := by
  unfold LGraph.localReg2_cendsMS
  rw [lwSymmFrame2_solid, Multiset.mem_coe]
  simp only [lwSymmFrame2P, List.map_cons, List.mem_cons, lwSymmTwistS_with_circ]
  left
  rfl

/-- `(Oe1x)`, the term `m Σ_α S_{xα} Ǧ_{αα} 𝒢`: the frame is kept, a leaf `α` joins the molecule of `x` and carries a blue loop (the colour
of the kept edge `e₀` at `x`). -/
theorem localReg2_pathFam_oe1xOwx (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe1xOwx c t m Γ p x).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe1xOwx owxT1
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ 0 ?_ ?_ h
  · exact localReg2_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [zero_add, localReg2_frame_cendsMS c t Γ p hp, localReg2_flip_flip_ms]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hmem : (true, s(μ (owxEmb 1 (Sum.inr x)), μ (owxEmb 1 v))) ∈
        localReg2_mapMS (fun w => μ (owxEmb 1 w)) (lwSymmFrame c t Γ p).localReg2_cendsMS := by
      have h1 := localReg2_mem_frame c t Γ p
      rw [hx] at h1
      exact Multiset.mem_map_of_mem (Prod.map id (Sym2.map fun w => μ (owxEmb 1 w))) h1
    have := localReg2_FamReplAt.add_loop hmem
    simpa [localReg2_mapMS, hα] using this

/-- `(Oe1x)`, the derivative term for the edge `q.1` of the rest: `e₀ = (x, v)` becomes `(α, v)` (the same molecular edge, `α ∈ M(x)`), `q.1` is
replaced through the molecule of `x` (by two edges of its colour). -/
theorem localReg2_pathFam_oe1xD (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xD m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xD
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    refine localReg2_VRepl.deriv μ (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) hα
      (SEdge.map (owxEmb 1) (lwSymmTwistS c t q.1)) 0 {(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 v))}
      {(true, s(Sum.inr (Sum.inr 0), owxEmb 1 v))} 0 (by simp) (by simp) (by simp) ?_ ?_ ?_ _
    · simp only [localReg2_mapMS, Multiset.map_singleton, Prod.map_apply, Sym2.map_mk, hα, id_eq]
    · rw [hx]; localReg2_msnorm
    · localReg2_msnorm


/-- The image of an internal vertex under the embedding `owxEmb`. -/
theorem localReg2_owxEmb_inr_eq {E I : Type*} (k : ℕ) (x : I) : owxEmb k (Sum.inr x : E ⊕ I) = Sum.inr (Sum.inl x) := rfl

local macro "localReg2_msnormx" : tactic => `(tactic| (simp only [SEdge.localReg2_cends_mk, SEdge.localReg2_cends_map, Prod.map_apply, Sym2.map_mk, lwSymmTwistP, localReg2_mapMS, List.map_cons, List.map_nil, Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq, localReg2_owxEmb_inr_eq]; try abel))

/-- `(Oe1x)`, the term with the loop `Ǧ̄_{xx}` circled, for a red out-edge `q.1 = (x, d)` of `x`: `e_0` and `q.1` move from `x` to `α ∈ M(x)`, the
molecular edges are unchanged, the new red loop at `x` has the colour of `q.1`. -/
theorem localReg2_pathFam_oe1xP5 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (hσ : (lwSymmTwistS c t q.1).σ = false)
    (hs : (lwSymmTwistS c t q.1).src = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP5 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP5
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg2_cends = (false, s(Sum.inr x, (lwSymmTwistS c t q.1).dst)) := by
      simp [SEdge.localReg2_cends, hσ, hs]
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 v)),
        (false, s(owxEmb 1 (Sum.inr x), owxEmb 1 (lwSymmTwistS c t q.1).dst))}
      {(false, s(Sum.inr (Sum.inr 0), owxEmb 1 (lwSymmTwistS c t q.1).dst)), (true, s(Sum.inr (Sum.inr 0), owxEmb 1 v))}
      {(false, s(Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)))} (by simp) ?_ ?_ ?_ ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(false, s(owxEmb 1 (Sum.inr x), owxEmb 1 (lwSymmTwistS c t q.1).dst)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff] at hC ⊢
      rcases hC with hC | hC <;> exact Or.inl hC
    · localReg2_simp0
      simp only [hα]
      abel
    · rw [hx, hqe]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe1x)`, the term with the loop `Ḡ_{xx}` replaced by the constant `m̄`, for a red out-edge of `x`: the molecular edges are unchanged. -/
theorem localReg2_pathFam_oe1xP3 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (hσ : (lwSymmTwistS c t q.1).σ = false)
    (hs : (lwSymmTwistS c t q.1).src = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP3 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP3
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg2_cends = (false, s(Sum.inr x, (lwSymmTwistS c t q.1).dst)) := by
      simp [SEdge.localReg2_cends, hσ, hs]
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 v)),
        (false, s(owxEmb 1 (Sum.inr x), owxEmb 1 (lwSymmTwistS c t q.1).dst))}
      {(false, s(Sum.inr (Sum.inr 0), owxEmb 1 (lwSymmTwistS c t q.1).dst)), (true, s(Sum.inr (Sum.inr 0), owxEmb 1 v))}
      0 (by simp) (by simp) (by simp) ?_ ?_ ?_ _
    · localReg2_simp0
      simp only [hα]
      abel
    · rw [hx, hqe]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe1x)`, the term with the loop `Ǧ_{xx}` circled, for a blue in-edge `q.1 = (s, x)` of `x`: the molecular edges are unchanged. -/
theorem localReg2_pathFam_oe1xP6 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (hσ : (lwSymmTwistS c t q.1).σ = true)
    (hd : (lwSymmTwistS c t q.1).dst = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP6 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP6
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg2_cends = (true, s((lwSymmTwistS c t q.1).src, Sum.inr x)) := by
      simp [SEdge.localReg2_cends, hσ, hd]
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 v)),
        (true, s(owxEmb 1 (lwSymmTwistS c t q.1).src, owxEmb 1 (Sum.inr x)))}
      {(true, s(owxEmb 1 (lwSymmTwistS c t q.1).src, Sum.inr (Sum.inr 0))), (true, s(Sum.inr (Sum.inr 0), owxEmb 1 v))}
      {(true, s(Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)))} (by simp) ?_ ?_ ?_ ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 v)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff] at hC ⊢
      rcases hC with hC | hC <;> exact Or.inl hC
    · localReg2_simp0
      simp only [hα]
      abel
    · rw [hx, hqe]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe1x)`, the term with the loop `G_{xx}` replaced by the constant `m`, for a blue in-edge of `x`: the molecular edges are unchanged. -/
theorem localReg2_pathFam_oe1xP4 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (hσ : (lwSymmTwistS c t q.1).σ = true)
    (hd : (lwSymmTwistS c t q.1).dst = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP4 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP4
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg2_cends = (true, s((lwSymmTwistS c t q.1).src, Sum.inr x)) := by
      simp [SEdge.localReg2_cends, hσ, hd]
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 v)),
        (true, s(owxEmb 1 (lwSymmTwistS c t q.1).src, owxEmb 1 (Sum.inr x)))}
      {(true, s(owxEmb 1 (lwSymmTwistS c t q.1).src, Sum.inr (Sum.inr 0))), (true, s(Sum.inr (Sum.inr 0), owxEmb 1 v))}
      0 (by simp) (by simp) (by simp) ?_ ?_ ?_ _
    · localReg2_simp0
      simp only [hα]
      abel
    · rw [hx, hqe]; localReg2_msnorm
    · localReg2_msnorm


/-- The frame of two selected edges has the molecules (the adjacency) of the graph. -/
theorem localReg2_lwSymmFrame2_adj (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).adj = Γ.adj := localReg_lwSymmFrame2_adj c t Γ p q

/-- `(Oe2x)`, `R2` (`m³ S⁺_{xy} G_{y'y} f`): the waved edge `x ~ y` merges the molecules of `x` and `y`, `p.1 = (x, y)` becomes a loop,
`q.1 = (y', x)` becomes `(y', y)`. -/
theorem localReg2_pathFam_oe2xR2 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR2 c t m Γ p q x y y').localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR2 oe2xR2
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨w, SimpleGraph.Reachable.refl _⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hxy : μ (Sum.inr x) = μ y :=
      hμ _ _ (LGraph.localReg_reach_of_waved _ ⟨true, true, Sum.inr x, y⟩ (by simp [LGraph.owxExt]))
    refine localReg2_VRepl.same μ {(true, s(Sum.inr x, y))} {(true, s(y', Sum.inr x))} {(true, s(y', y))} 0
      (by simp [Sym2.mk_isDiag_iff, hxy]) (by simp) (by simp) ?_ ?_ ?_ _
    · simp only [localReg2_mapMS, Multiset.map_singleton, Prod.map_apply, Sym2.map_mk, hxy, id_eq]
    · rw [hp1, hq1]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe2x)`, `R3 = (Owx)` term 1 on the frame: a leaf `α` joins the molecule of `x` and carries a blue loop (the colour of the kept `p.1`). -/
theorem localReg2_pathFam_oe2xR3 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR3 c t m Γ p q x).localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR3 owxT1
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ 0 ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [zero_add, localReg2_frame2_cendsMS c t Γ p q hp hq, localReg2_flip_flip_ms]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hmem : (true, s(μ (owxEmb 1 (Sum.inr x)), μ (owxEmb 1 y))) ∈
        localReg2_mapMS (fun w => μ (owxEmb 1 w)) (lwSymmFrame2 c t Γ p q).localReg2_cendsMS := by
      have h1 := localReg2_mem_frame2 c t Γ p q
      rw [hp1] at h1
      exact Multiset.mem_map_of_mem (Prod.map id (Sym2.map fun w => μ (owxEmb 1 w))) h1
    have := localReg2_FamReplAt.add_loop hmem
    simpa [localReg2_mapMS, hα] using this

/-- `(Oe2x)`, `R4`: the edges `(x, y)`, `(y', x)` move to `(α, y)`, `(y', α)` with `α ∈ M(x)`, a blue loop at `β ∈ M(x)` is added. -/
theorem localReg2_pathFam_oe2xR4 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR4 c t m Γ p q x y y').localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR4 oe2xR4
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 2 (Sum.inr x) w, lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 2 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (owxEmb 2 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 (Sum.inr x), owxEmb 2 y)), (true, s(owxEmb 2 y', owxEmb 2 (Sum.inr x)))}
      {(true, s(Sum.inr (Sum.inr 0), owxEmb 2 y)), (true, s(owxEmb 2 y', Sum.inr (Sum.inr 0)))}
      {(true, s(Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)))} (by simp) ?_ ?_ ?_ ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(true, s(owxEmb 2 (Sum.inr x), owxEmb 2 y)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff, hβ] at hC ⊢
      rcases hC with hC | hC <;> exact Or.inl hC
    · localReg2_simp0
      simp only [hα]
      try abel
    · rw [hp1, hq1]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe2x)`, `R5`: the edges `(x, y)`, `(y', x)` move to `(α, y)`, `(y', α)` with `α ∈ M(x)`, a blue loop at `x` is added. -/
theorem localReg2_pathFam_oe2xR5 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR5 c t m Γ p q x y y').localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR5 oe2xR5
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 y)), (true, s(owxEmb 1 y', owxEmb 1 (Sum.inr x)))}
      {(true, s(Sum.inr (Sum.inr 0), owxEmb 1 y)), (true, s(owxEmb 1 y', Sum.inr (Sum.inr 0)))}
      {(true, s(Sum.inr (Sum.inl x), Sum.inr (Sum.inl x)))} (by simp) ?_ ?_ ?_ ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(true, s(owxEmb 1 (Sum.inr x), owxEmb 1 y)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff] at hC ⊢
      rcases hC with hC | hC <;> exact Or.inl hC
    · localReg2_simp0
      simp only [hα]
      try abel
    · rw [hp1, hq1]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe2x)`, `R6`: the edges `(x, y)`, `(y', x)` move to `(β, y)`, `(y', β)` with `β ∈ M(x)`, a blue loop at `α ∈ M(x)` is added. -/
theorem localReg2_pathFam_oe2xR6 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR6 c t m Γ p q x y y').localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR6 oe2xR6
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 2 (Sum.inr x) w, lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) w⟩
  · exact localReg2_hΓ_two Γ p hp q hq c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 2 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (owxEmb 2 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg2_VRepl.same μ 0 {(true, s(owxEmb 2 (Sum.inr x), owxEmb 2 y)), (true, s(owxEmb 2 y', owxEmb 2 (Sum.inr x)))}
      {(true, s(Sum.inr (Sum.inr 1), owxEmb 2 y)), (true, s(owxEmb 2 y', Sum.inr (Sum.inr 1)))}
      {(true, s(Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)))} (by simp) ?_ ?_ ?_ ?_ ?_ _
    · simp [Sym2.mk_isDiag_iff]
    · refine localReg2_cov_of_forall μ ?_
      intro s hs
      simp only [Multiset.mem_singleton] at hs
      subst hs
      refine ⟨(true, s(owxEmb 2 (Sum.inr x), owxEmb 2 y)), by simp, rfl, ?_⟩
      intro C hC
      simp only [Sym2.map_mk, Sym2.mem_iff, hα] at hC ⊢
      rcases hC with hC | hC <;> exact Or.inl hC
    · localReg2_simp0
      simp only [hβ]
      try abel
    · rw [hp1, hq1]; localReg2_msnorm
    · localReg2_msnorm

/-- `(Oe2x)`, `R7` for the edge `q'.1` of `f`: `(x, y)` becomes `(α, y)`, `(y', x)` stays, `q'.1` is replaced by the two edges of its derivative through
`M(x)` (of its colour). -/
theorem localReg2_pathFam_oe2xR7 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR7 c t m Γ p q x y y' q').localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR7 oe2xR7
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ (lwSymmTwistS c t q'.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · exact localReg2_hΓ_three Γ p hp q hq q' hq' c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (Sum.inr (Sum.inl x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    refine localReg2_VRepl.deriv μ (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) hα
      (SEdge.map (owxEmb 1) (lwSymmTwistS c t q'.1)) 0
      {(true, s(Sum.inr (Sum.inl x), owxEmb 1 y)), (true, s(owxEmb 1 y', Sum.inr (Sum.inl x)))}
      {(true, s(owxEmb 1 y', Sum.inr (Sum.inl x))), (true, s(Sum.inr (Sum.inr 0), owxEmb 1 y))} 0
      (by simp) (by simp) (by simp) ?_ ?_ ?_ _
    · localReg2_simp0
      simp only [hα]
      abel
    · rw [hp1, hq1]; localReg2_msnormx
    · localReg2_msnormx

/-- `(Oe2x)`, `R8` for the edge `q'.1` of `f`: `(x, y)`, `(y', x)` move to `(β, y)`, `(y', α)`, `q'.1` is replaced by its derivative at `(β, α)` through
`M(x)` (of its colour). -/
theorem localReg2_pathFam_oe2xR8 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) {k : ℕ} {a b : E}
    (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR8 c t m Γ p q x y y' q').localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR8 oe2xR8
  refine localReg2_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg2_cends ::ₘ (lwSymmTwistS c t q.1).localReg2_cends ::ₘ (lwSymmTwistS c t q'.1).localReg2_cends ::ₘ 0) ?_ ?_ h
  · exact localReg2_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 2 (Sum.inr x) w, lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) w⟩
  · exact localReg2_hΓ_three Γ p hp q hq q' hq' c t
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (Sum.inr (Sum.inl x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (Sum.inr (Sum.inl x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg2_VRepl.deriv μ (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (hβ.trans hα.symm)
      (SEdge.map (owxEmb 2) (lwSymmTwistS c t q'.1)) 0
      {(true, s(Sum.inr (Sum.inl x), owxEmb 2 y)), (true, s(owxEmb 2 y', Sum.inr (Sum.inl x)))}
      {(true, s(Sum.inr (Sum.inr 1), owxEmb 2 y)), (true, s(owxEmb 2 y', Sum.inr (Sum.inr 0)))} 0
      (by simp) (by simp) (by simp) ?_ ?_ ?_ _
    · localReg2_simp0
      simp only [hα, hβ]
      try abel
    · rw [hp1, hq1]; localReg2_msnormx
    · localReg2_msnormx

end GraphLevel2

/-! ## 4. The invariant along a `LocStep` -/

section Assembly2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The coloured invariant for every term of `lwSymmOe1xDs` (the derivative terms of `(Oe1x)`). -/
theorem localReg2_pathFam_oe1xDs (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (T : LGraph E (I ⊕ Fin 1))
    (hT : T ∈ lwSymmOe1xDs c t m Γ p x v q) {k : ℕ} {a b : E} (h : Γ.localReg2_PathFam k (Sum.inl a) (Sum.inl b)) :
    T.localReg2_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe1xDs at hT
  obtain ⟨T0, hT0, rfl⟩ := List.mem_map.1 hT
  unfold oe1xDs at hT0
  by_cases h1 : (lwSymmTwistP c t q).1.σ = false ∧ (lwSymmTwistP c t q).1.src = Sum.inr x
  · simp only [h1, and_self, ↓reduceIte] at hT0
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT0
    rcases hT0 with rfl | rfl
    · exact localReg2_pathFam_oe1xP5 m Γ p hp x v c t hx q hq h1.1 h1.2 h
    · exact localReg2_pathFam_oe1xP3 m Γ p hp x v c t hx q hq h1.1 h1.2 h
  · simp only [h1, ↓reduceIte] at hT0
    by_cases h2 : (lwSymmTwistP c t q).1.σ = true ∧ (lwSymmTwistP c t q).1.dst = Sum.inr x
    · simp only [h2, and_self, ↓reduceIte] at hT0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT0
      rcases hT0 with rfl | rfl
      · exact localReg2_pathFam_oe1xP6 m Γ p hp x v c t hx q hq h2.1 h2.2 h
      · exact localReg2_pathFam_oe1xP4 m Γ p hp x v c t hx q hq h2.1 h2.2 h
    · simp only [h2, ↓reduceIte] at hT0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT0
      rw [hT0]
      exact localReg2_pathFam_oe1xD m Γ p hp x v c t hx q hq h

/-- **The coloured path invariant of a packed graph with two external vertices** `x = Q.ext 0`, `y = Q.ext 1`: `p` walks in the molecular multigraph
from the molecule of `x` to that of `y`, each of one colour, using every non-loop molecular edge exactly once with its colour, with the Hall condition
on the internal molecules, and such that every colour present at a molecule is carried by a walk visiting it. -/
def PGraph.PathInv2 (p : ℕ) (Q : PGraph (Fin 2)) : Prop :=
  Q.g.localReg2_PathFam p (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1))

/-- **The coloured invariant passes along every `LocStep`** (the cases of `B:178-199` for the outputs of `(Owx)`, `(Oe1x)`, `(Oe2x)` after the dotted edge
partition). -/
theorem pathInv2_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs) {k : ℕ}
    (hP : P.PathInv2 k) : ∀ B ∈ outs, B.PathInv2 k := by
  have key : ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I''),
      T.localReg2_PathFam k (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) →
        ∀ Q0 ∈ T.partition m, (Q0.lvl1Comp P.ext P.ext_surj).PathInv2 k :=
    fun T hT Q0 hQ0 => LGraph.localReg2_pathFam_partition m T Q0 hQ0 hT
  intro B hB
  cases hst with
  | weight p hp x c t hx =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1WeightOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with ((hQ | hQ) | ⟨q, hq, hQ⟩) | ⟨q, hq, hQ⟩
    · exact key _ (localReg2_pathFam_owxT1 m P.g p hp x c t hx hP) Q0 hQ
    · exact key _ (localReg2_pathFam_owxT2 m P.g p hp x c t hx hP) Q0 hQ
    · exact key _ (localReg2_pathFam_owxT3 m P.g p hp x c t hx q hq hP) Q0 hQ
    · exact key _ (localReg2_pathFam_owxT4 m P.g p hp x c t hx q hq hP) Q0 hQ
  | edge p hp x v hv c t hx hwf hbad =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1EdgeOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with hQ | ⟨q, hq, T, hT, hQ⟩
    · exact key _ (localReg2_pathFam_oe1xOwx m P.g p hp x v c t hx hP) Q0 hQ
    · exact key T (localReg2_pathFam_oe1xDs m P.g p hp x v c t hx q hq T hT hP) Q0 hQ
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1GGOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with (((((hQ | hQ) | hQ) | hQ) | hQ) | ⟨q', hq', hQ⟩) | ⟨q', hq', hQ⟩
    · exact key _ (localReg2_pathFam_oe2xR2 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg2_pathFam_oe2xR3 m P.g p q hp hq x y c t hp1 hP) Q0 hQ
    · exact key _ (localReg2_pathFam_oe2xR4 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg2_pathFam_oe2xR5 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg2_pathFam_oe2xR6 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg2_pathFam_oe2xR7 m P.g p q hp hq x y y' c t hp1 hq1 q' hq' hP) Q0 hQ
    · exact key _ (localReg2_pathFam_oe2xR8 m P.g p q hp hq x y y' c t hp1 hq1 q' hq' hP) Q0 hQ


end Assembly2

/-! ## 5. The starting graph `|f_{xy}(G)|^p` -/

section Start2

/-- **The walks of the starting graph, with colours**: `x → α_i → y` through the molecule `{α_i, β_i}`, of the colour of the block `i`
(blue for `i < p / 2`); every non-loop molecular edge lies on exactly one walk and has its colour; the colour of every edge at a molecule is
carried by the walk of its block. -/
theorem localReg2_fxyPowGraph_pathFam (p : ℕ) : (fxyPowGraph p).localReg2_PathFam p (Sum.inl 0) (Sum.inl 1) := by
  classical
  set Mx := (fxyPowGraph p).molOf (Sum.inl 0) with hMx
  set My := (fxyPowGraph p).molOf (Sum.inl 1) with hMy
  have hxi : ∀ i : Fin p, Mx ≠ localReg_fxyMol i := fun i h => localReg_fxyMol_internal i ⟨0, h⟩
  have hiy : ∀ i : Fin p, localReg_fxyMol i ≠ My := fun i h => localReg_fxyMol_internal i ⟨1, h.symm⟩
  have hβ : ∀ i : Fin p, (fxyPowGraph p).molOf (Sum.inr (localReg_fxyBeta i)) = localReg_fxyMol i := fun i => by
    unfold localReg_fxyMol
    rw [localReg_fxy_molOf_eq_iff, localReg_fxy_blk_alpha, localReg_fxy_blk_beta]
  have hα : ∀ i : Fin p, (fxyPowGraph p).molOf (Sum.inr (localReg_fxyAlpha i)) = localReg_fxyMol i := fun i => rfl
  have hs : (fxyPowGraph p).solid = (List.finRange p).flatMap (localReg_fxyBlock p) := rfl
  refine ⟨fun i => [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)], fun i => decide (i.1 < p / 2), fun i => ?_, ?_, ?_, ?_⟩
  · exact localReg_StepWalk.cons _ _ _ _ (localReg_StepWalk.cons _ _ _ _ (localReg_StepWalk.nil _))
  · have hblock : ∀ i : Fin p, localReg2_offDiag
        ((((localReg_fxyBlock p i).map (Prod.map id (Sym2.map (fxyPowGraph p).molOf) ∘ SEdge.localReg2_cends) :
          List (Bool × Sym2 (fxyPowGraph p).Mol)) : Multiset (Bool × Sym2 (fxyPowGraph p).Mol))) =
        (localReg_stepEdges [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)]).map (fun s => (decide (i.1 < p / 2), s)) := by
      intro i
      unfold localReg2_offDiag
      rw [Multiset.filter_coe]
      simp [localReg_fxyBlock, SEdge.localReg2_cends, localReg_stepEdges, hβ i, hα i, Sym2.mk_isDiag_iff, ← hMx, ← hMy, hxi i, hiy i, List.filter_cons]
    have hR : localReg2_offDiag (fxyPowGraph p).localReg2_edgeMS =
        ∑ i : Fin p, (localReg_stepEdges [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)]).map (fun s => (decide (i.1 < p / 2), s)) := by
      unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS
      rw [Multiset.map_coe, List.map_map, hs, List.map_flatMap, localReg_coe_flatMap_eq_sum, ← Fin.sum_univ_def, localReg2_offDiag_sum]
      exact Finset.sum_congr rfl fun i _ => hblock i
    have hL : localReg2_offDiag (localReg2_stepMS (fun i : Fin p => decide (i.1 < p / 2))
        (fun i => [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)])) =
        ∑ i : Fin p, (localReg_stepEdges [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)]).map (fun s => (decide (i.1 < p / 2), s)) := by
      refine localReg2_offDiag_eq_self ?_
      intro s hs'
      unfold localReg2_stepMS at hs'
      obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hs'
      obtain ⟨s', hs'', rfl⟩ := Multiset.mem_map.1 hi
      simp only [localReg_stepEdges, List.map_cons, List.map_nil, Multiset.cons_coe, Multiset.mem_cons, Multiset.coe_nil] at hs''
      simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hs''
      rcases hs'' with rfl | rfl
      · simpa [Sym2.mk_isDiag_iff] using hxi i
      · simpa [Sym2.mk_isDiag_iff] using hiy i
    rw [hL, hR]
  · intro A hA
    let S : Finset (Fin p) := Finset.univ.filter fun i => localReg_fxyMol i ∈ A
    have hAsub : A ⊆ S.image localReg_fxyMol := by
      intro c hc
      obtain ⟨i, rfl⟩ := localReg_fxy_internal_eq c (fun a ha => hA c hc ⟨a, ha⟩)
      exact Finset.mem_image.2 ⟨i, by simp [S, hc], rfl⟩
    have h1 : A.card ≤ S.card := (Finset.card_le_card hAsub).trans Finset.card_image_le
    refine h1.trans (Finset.card_le_card ?_)
    intro i hi
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨localReg_fxyMol i, hi, Or.inr ⟨(Mx, localReg_fxyMol i), by simp, rfl⟩⟩
  · rintro C σ ⟨s, hs', h1, h2⟩
    unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS at hs'
    rw [Multiset.map_coe, List.map_map, Multiset.mem_coe, List.mem_map] at hs'
    obtain ⟨e, he, rfl⟩ := hs'
    obtain ⟨i, hi⟩ := (localReg_fxy_mem_solid e).1 he
    simp only [localReg_fxyBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    have hvM : localReg_StepWalk.Visits Mx [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)] Mx := Or.inl rfl
    have hvI : localReg_StepWalk.Visits Mx [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)] (localReg_fxyMol i) :=
      Or.inr ⟨(Mx, localReg_fxyMol i), by simp, rfl⟩
    have hvY : localReg_StepWalk.Visits Mx [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)] My :=
      Or.inr ⟨(localReg_fxyMol i, My), by simp, rfl⟩
    rcases hi with rfl | rfl | rfl
    · simp only [Function.comp_apply, SEdge.localReg2_cends_mk, Prod.map_apply, Sym2.map_mk, id_eq, hβ i] at h1 h2
      simp only [Sym2.mem_iff, or_self] at h2
      exact ⟨i, h1, h2 ▸ hvI⟩
    · simp only [Function.comp_apply, SEdge.localReg2_cends_mk, Prod.map_apply, Sym2.map_mk, id_eq, hα i] at h1 h2
      simp only [Sym2.mem_iff] at h2
      rcases h2 with rfl | rfl
      · exact ⟨i, h1, hvM⟩
      · exact ⟨i, h1, hvI⟩
    · simp only [Function.comp_apply, SEdge.localReg2_cends_mk, Prod.map_apply, Sym2.map_mk, id_eq, hα i] at h1 h2
      simp only [Sym2.mem_iff] at h2
      rcases h2 with rfl | rfl
      · exact ⟨i, h1, hvI⟩
      · exact ⟨i, h1, hvY⟩

/-- The starting graph carries the coloured path invariant. -/
theorem fxyPowGraph_pathInv2 (p : ℕ) : (fxyPowGraph p).pack.PathInv2 p := localReg2_fxyPowGraph_pathFam p


end Start2

/-! ## 6. Property (4): the invariant at a locally standard graph -/

section Final2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Forgetting the colours of the molecular edges gives the (uncoloured) molecular edges. -/
theorem LGraph.localReg2_edgeMS_snd (Γ : LGraph E I) : Γ.localReg2_edgeMS.map Prod.snd = Γ.localReg_edgeMS := by
  unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS LGraph.localReg_edgeMS LGraph.localReg_endsMS localReg2_mapMS
  rw [Multiset.map_coe, Multiset.map_coe, Multiset.map_coe, List.map_map, List.map_map, List.map_map]
  rfl

/-- The non-diagonal part commutes with forgetting the colours. -/
theorem localReg2_offDiag_snd {N : Type*} (m : Multiset (Bool × Sym2 N)) :
    (localReg2_offDiag m).map Prod.snd = localReg_offDiag (m.map Prod.snd) := by
  unfold localReg2_offDiag localReg_offDiag
  rw [Multiset.filter_map]
  rfl

/-- Forgetting the colours of the steps of a family of walks gives the steps. -/
theorem localReg2_stepMS_snd {N : Type*} {p : ℕ} (col : Fin p → Bool) (W : Fin p → List (N × N)) :
    (localReg2_stepMS col W).map Prod.snd = ∑ i, localReg_stepEdges (W i) := by
  unfold localReg2_stepMS
  have h := map_sum (Multiset.mapAddMonoidHom (Prod.snd : Bool × Sym2 N → Sym2 N))
    (fun i => (localReg_stepEdges (W i)).map fun s => (col i, s)) Finset.univ
  rw [Multiset.coe_mapAddMonoidHom] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.map_map]
  exact Multiset.map_id' _

/-- A solid edge gives a coloured molecular edge. -/
theorem LGraph.localReg2_mem_edgeMS (Γ : LGraph E I) {e : SEdge (E ⊕ I)} (he : e ∈ Γ.solid) :
    Prod.map id (Sym2.map Γ.molOf) e.localReg2_cends ∈ Γ.localReg2_edgeMS := by
  unfold LGraph.localReg2_edgeMS localReg2_mapMS
  exact Multiset.mem_map_of_mem _ (by unfold LGraph.localReg2_cendsMS; rw [Multiset.mem_coe]; exact List.mem_map_of_mem he)

/-- **In a locally standard graph, both colours are present at every internal molecule that has an edge at it**: a vertex incident to a solid edge is
standard neutral, so it has one blue and one red edge. -/
theorem LGraph.localReg2_present_of_locStd (Γ : LGraph E I) (hL : Γ.LocStd) {C : Γ.Mol} (hC : ∀ a : E, Γ.molOf (Sum.inl a) ≠ C)
    {e : SEdge (E ⊕ I)} (he : e ∈ Γ.solid) (hCe : C = Γ.molOf e.src ∨ C = Γ.molOf e.dst) (σ : Bool) :
    localReg2_present Γ.localReg2_edgeMS C σ := by
  have hv : ∃ v : E ⊕ I, Γ.molOf v = C ∧ (e.src = v ∨ e.dst = v) := by
    rcases hCe with h | h
    · exact ⟨e.src, h.symm, Or.inl rfl⟩
    · exact ⟨e.dst, h.symm, Or.inr rfl⟩
  obtain ⟨v, hvC, hve⟩ := hv
  rcases v with a | i
  · exact absurd hvC (hC a)
  · have hinc : e.lvl1IncAt (Sum.inr i) = true := (lvl1_incAt_iff e _).2 ⟨hL.2.1 e he, hve⟩
    have hmem : e ∈ Γ.lvl1SolidAt (Sum.inr i) := List.mem_filter.2 ⟨he, hinc⟩
    have hdeg : Γ.lvl1DegAt (Sum.inr i) ≠ 0 := by
      unfold LGraph.lvl1DegAt
      exact (List.length_pos_of_mem hmem).ne'
    rcases hL.2.2 i with hstd | hz
    · have hσ : σ ∈ (Γ.lvl1SolidAt (Sum.inr i)).map SEdge.σ := by
        rcases hstd.1 with h | h <;> rw [h] <;> cases σ <;> simp
      obtain ⟨e', he', hσ'⟩ := List.mem_map.1 hσ
      obtain ⟨he's, hinc'⟩ := List.mem_filter.1 he'
      have hend := ((lvl1_incAt_iff e' _).1 hinc').2
      refine ⟨Prod.map id (Sym2.map Γ.molOf) e'.localReg2_cends, ?_, hσ', ?_⟩
      · exact Γ.localReg2_mem_edgeMS he's
      · rw [← hvC]
        simp only [SEdge.localReg2_cends, Prod.map_apply, Sym2.map_mk]
        rcases hend with h | h
        · rw [h]; exact Sym2.mem_mk_left _ _
        · rw [h]; exact Sym2.mem_mk_right _ _
    · exact absurd hz hdeg

/-- **Property (4) from the coloured invariant at a locally standard graph** (with (3) and (5) for the same family of walks): the invariant gives walks of the
colour carried by every edge at a molecule; at a locally standard graph an internal molecule with an edge has both colours, hence is visited by a blue and
a red walk, which are different walks. -/
theorem PGraph.PathInv2.locReg345 {Q : PGraph (Fin 2)} {p : ℕ} (hL : Q.LocStd) (h : Q.PathInv2 p) : Q.LocReg345 p := by
  obtain ⟨W, col, hW, hE, hH, hLc⟩ := h
  refine ⟨fun i => localReg_stepStrip (W i), ⟨fun i => (hW i).strip.1, ?_⟩, ?_, ?_⟩
  · -- (3): the budget
    have h1 : ∑ i, localReg_stepEdges (localReg_stepStrip (W i)) = Q.g.localReg_molEdgeMS := by
      simp only [localReg_stepEdges_strip]
      rw [← localReg_offDiag_sum, ← localReg2_stepMS_snd col W, ← localReg2_offDiag_snd, hE, localReg2_offDiag_snd,
        LGraph.localReg2_edgeMS_snd, LGraph.localReg_offDiag_edgeMS]
    exact h1.le
  · -- (4)
    intro C hC
    have h1 := hH {C} (by simpa using hC)
    rw [Finset.card_singleton] at h1
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (Nat.succ_le_iff.1 h1)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left] at hj
    have hjs := (hW j).strip.2 C hj
    rcases hjs with hCu | ⟨st, hst, hstC⟩
    · exact absurd ⟨Q.ext 0, hCu.symm⟩ hC
    · obtain ⟨hstW, hne⟩ := List.mem_filter.1 hst
      have hne' : st.1 ≠ st.2 := by simpa using hne
      have hmem : (col j, s(st.1, st.2)) ∈ localReg2_stepMS col W := by
        unfold localReg2_stepMS
        exact Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, Multiset.mem_map.2 ⟨s(st.1, st.2), localReg_mem_stepEdges.2 ⟨st, hstW, rfl⟩, rfl⟩⟩
      have hmem' : (col j, s(st.1, st.2)) ∈ localReg2_offDiag (localReg2_stepMS col W) :=
        localReg2_mem_offDiag.2 ⟨hmem, by simpa [Sym2.mk_isDiag_iff] using hne'⟩
      rw [hE] at hmem'
      obtain ⟨hmem2, -⟩ := localReg2_mem_offDiag.1 hmem'
      unfold LGraph.localReg2_edgeMS localReg2_mapMS LGraph.localReg2_cendsMS at hmem2
      rw [Multiset.map_coe, Multiset.mem_coe, List.mem_map] at hmem2
      obtain ⟨e', he', hee'⟩ := hmem2
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      have hC' : Q.g.molOf e.src = C ∨ Q.g.molOf e.dst = C := by
        have h2 := congrArg Prod.snd hee'
        simp only [SEdge.localReg2_cends, Prod.map_apply, Sym2.map_mk] at h2
        have h3 : C ∈ (s(Q.g.molOf e.src, Q.g.molOf e.dst) : Sym2 Q.g.Mol) := by
          rw [h2, ← hstC]
          exact Sym2.mem_mk_right _ _
        rcases Sym2.mem_iff.1 h3 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hCe : C = Q.g.molOf e.src ∨ C = Q.g.molOf e.dst := by
        rcases hC' with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      obtain ⟨ib, hib1, hib2⟩ := hLc C true (Q.g.localReg2_present_of_locStd hL (fun a ha => hC ⟨a, ha⟩) he hCe true)
      obtain ⟨ir, hir1, hir2⟩ := hLc C false (Q.g.localReg2_present_of_locStd hL (fun a ha => hC ⟨a, ha⟩) he hCe false)
      refine ⟨ib, ir, ?_, (hW ib).strip.2 C hib2, (hW ir).strip.2 C hir2⟩
      intro hbr
      rw [hbr] at hib1
      rw [hib1] at hir1
      exact Bool.noConfusion hir1
  · -- (5)
    intro A hA
    refine (hH A hA).trans (Finset.card_le_card ?_)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨c, hc, hv⟩ := hi
    exact ⟨c, hc, (hW i).strip.2 c hv⟩

end Final2

/-! ## 7. The expansion theorem `lw_localregular_upto5` -/

section Expansion2

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- **`lem:localregular`, properties (1)-(5)**: the local expansion of `|f_{xy}(G)|^p` into locally standard graphs and the path properties
(`7_8:786-821`, proof `B:172-199`), now with property (4).  The lists `outs`, `errs` and the expectation identity `(eq:local_Gs)` are those of
`lvl1_lemma_size` for the starting graph `(fxyPowGraph p).pack`; every graph of `outs` satisfies (1) locally standard, (2) `n_M ≤ p` and
`(eq:MolVW)`, and (3), (4), (5) for one common family of walks.  No assumption `(eq:far_ab)` is made; property (6) is not part of this statement
(LW-10c). -/
theorem lw_localregular_upto5 (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧
        Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
        (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧
      (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
        (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
        (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
        (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n),
          ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
            (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
            (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p) := by
  obtain ⟨outs, errs, hA, hB, hC, hD⟩ :=
    lvl1_lemma_size (E := Fin 2) m c hc K0 d D (fxyPowGraph p).pack (fxyPowGraph_normal p)
  have hP : ∀ Q ∈ outs ++ errs, Q.PathInv2 p := fun Q hQ =>
    lvl1_induction (hC Q hQ).1 (fun Q : PGraph (Fin 2) => Q.PathInv2 p) (fxyPowGraph_pathInv2 p)
      (fun A L hst hA B hB => pathInv2_locStep hst hA B hB)
  refine ⟨outs, errs, hA, hB, hC, hD, fun Q hQ => ?_⟩
  have hQ' : Q ∈ outs ++ errs := List.mem_append_left _ hQ
  refine ⟨(hA Q hQ).1, ⟨?_, fun c => Q.g.molNV_le_molNW_add_one (hC Q hQ').2.1 c⟩, (hP Q hQ').locReg345 (hA Q hQ).1⟩
  have := (hC Q hQ').2.2.2.1
  rw [show (fxyPowGraph p).pack.g.nM = p from (fxyPowGraph_counters p).2.2.2] at this
  exact this

end Expansion2

/-! ## 8. Compiled instances -/

section Instances2

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- **The coloured invariant at the starting graphs** `p = 2`, `p = 4`. -/
example : (fxyPowGraph 2).pack.PathInv2 2 := fxyPowGraph_pathInv2 2

example : (fxyPowGraph 4).pack.PathInv2 4 := fxyPowGraph_pathInv2 4

/-- **The coloured invariant along one `LocStep`**: Step 1 of `strat_local` at the light-weight `(Ǧ - M)_{β₁β₁}` of `p2Graph = fxyPowGraph 2`
(the merged `lvl1_inst_locStep_weight`): every output carries the coloured invariant. -/
theorem localReg2_inst_step1 :
    ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false), B.PathInv2 2 :=
  pathInv2_locStep lvl1_inst_locStep_weight (fxyPowGraph_pathInv2 2)

/-- **`lw_localregular_upto5` at `p = 2`**, `d = 3`, `c = 1/4`, `K0 = 1` (`L^3 ≤ W`), `D = 10`; the regime is evaluated at `W = 27`, `L = 3`,
`Ψ = 27^{-1/4}`; the expectation identity holds at the merged instance data of `Graph/LWWeightExp.lean` (`lwWxInstSz`: `d = 3`, `L = 3`, `W = 1`,
`m = i`, `z = zt 0 (1/2)`, `u = 1/2`) with every hypothesis discharged. -/
theorem localReg2_inst_expansion :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
      ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum ∧
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg345 2) := by
  obtain ⟨outs, errs, h1, h2, -, hid, h5⟩ :=
    lw_localregular_upto5 2 (mE 0) (1 / 4) (by norm_num) 1 3 10
  refine ⟨outs, errs, fun Q hQ => ?_, fun Q hQ => ?_, ?_, h5⟩
  · obtain ⟨a, b⟩ := h1 Q hQ
    have e : (fxyPowGraph 2).pack.g.scalingOrder = 2 := fxyPowGraph_ord 2
    exact ⟨a, by rw [e] at b; exact b⟩
  · refine h2 Q hQ 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_ (le_refl _)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · exact hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) (lwWx_mE_ne 0 lwWx_inst_hE)
      (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 lwSymmInstL

/-- A small locally standard graph for the instance of property (4): the external vertices `x = inl 0`, `y = inl 1`, the internal vertices
`α = inr 0`, `β = inr 1` joined by the waved edge `S_{αβ}`; `G_{xα}`, `Ḡ_{xα}` at `α` and `G_{βy}`, `Ḡ_{βy}` at `β` (every internal vertex has one
blue and one red edge, neutral charge), and the `×`-dotted edges of the solid pairs.  One internal molecule `{α, β}`; two walks (a blue and a
red one) pass through it. -/
def localReg2_inst_Q : LGraph (Fin 2) (Fin 2) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨false, false, .inl 0, .inr 0⟩, ⟨true, false, .inr 1, .inl 1⟩, ⟨false, false, .inr 1, .inl 1⟩]
  waved := [⟨false, true, .inr 0, .inr 1⟩]
  dotted := [⟨false, .inr 0, .inl 0⟩, ⟨false, .inr 1, .inl 1⟩]
  coeff := 1

theorem localReg2_inst_Q_locStd : localReg2_inst_Q.LocStd := by decide

/-- **The coloured invariant holds at `localReg2_inst_Q` with `p = 2`**: the blue walk `x → {α,β} → y` uses `G_{xα}`, `G_{βy}`, the red one `Ḡ_{xα}`,
`Ḡ_{βy}`; every molecular edge lies on exactly one walk, of its colour. -/
theorem localReg2_inst_Q_pathInv2 : localReg2_inst_Q.pack.PathInv2 2 := by
  set Q := localReg2_inst_Q with hQ
  set Mx := Q.molOf (Sum.inl 0) with hMx
  set My := Q.molOf (Sum.inl 1) with hMy
  set C := Q.molOf (Sum.inr 0) with hC
  have hadj : Q.adj (Sum.inr 0) (Sum.inr 1) = true := by decide
  have hC1 : Q.molOf (Sum.inr 1) = C :=
    (SimpleGraph.ConnectedComponent.eq.2 (SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by decide, hadj⟩))).symm
  have hisoX : ∀ w, Q.adj (Sum.inl 0) w = false := by decide
  have hisoY : ∀ w, Q.adj (Sum.inl 1) w = false := by decide
  have hxC : Mx ≠ C := fun h => by
    have := Q.localReg_molOf_isolated (Sum.inl 0) hisoX (Sum.inr 0) h
    exact absurd this (by simp)
  have hyC : C ≠ My := fun h => by
    have := Q.localReg_molOf_isolated (Sum.inl 1) hisoY (Sum.inr 0) h.symm
    exact absurd this (by simp)
  have hint : ∀ c : Q.Mol, ¬ Q.IsExtMol c → c = C := by
    intro c hc
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases v with a | k
      · exact absurd ⟨a, rfl⟩ hc
      · fin_cases k
        · rfl
        · exact hC1
  show localReg2_Fam 2 Mx My (fun c => ¬ Q.IsExtMol c) Q.localReg2_edgeMS
  refine ⟨fun _ => [(Mx, C), (C, My)], ![true, false], fun i => ?_, ?_, ?_, ?_⟩
  · exact localReg_StepWalk.cons _ _ _ _ (localReg_StepWalk.cons _ _ _ _ (localReg_StepWalk.nil _))
  · have hE : Q.localReg2_edgeMS = ↑[(true, s(Mx, C)), (false, s(Mx, C)), (true, s(C, My)), (false, s(C, My))] := by
      unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS
      rw [Multiset.map_coe, List.map_map]
      simp [hQ, localReg2_inst_Q, SEdge.localReg2_cends, hC1, ← hMx, ← hMy, ← hC]
    have h1 : localReg2_offDiag Q.localReg2_edgeMS = Q.localReg2_edgeMS := by
      refine localReg2_offDiag_eq_self ?_
      intro s hs
      rw [hE] at hs
      simp only [Multiset.insert_eq_cons, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> simpa [Sym2.mk_isDiag_iff] using (by first | exact hxC | exact hyC)
    have h2 : localReg2_stepMS (![true, false] : Fin 2 → Bool) (fun _ : Fin 2 => [(Mx, C), (C, My)]) =
        Q.localReg2_edgeMS := by
      rw [hE]
      unfold localReg2_stepMS
      rw [Fin.sum_univ_two]
      simp only [localReg_stepEdges, List.map_cons, List.map_nil, Matrix.cons_val_zero, Matrix.cons_val_one, ← Multiset.cons_coe,
        Multiset.coe_nil, Multiset.map_cons, Multiset.map_zero, ← Multiset.singleton_add, add_zero, Multiset.map_add,
        Multiset.map_singleton]
      abel_nf
    rw [h2]
  · intro A hA
    have hAC : ∀ c ∈ A, c = C := fun c hc => hint c (hA c hc)
    by_cases hA0 : A = ∅
    · simp [hA0]
    · obtain ⟨c0, hc0⟩ := Finset.nonempty_iff_ne_empty.2 hA0
      have hsub : A ⊆ {C} := fun c hc => by simpa using hAC c hc
      have h1 : A.card ≤ 1 := by simpa using Finset.card_le_card hsub
      refine h1.trans ?_
      have h0 : (0 : Fin 2) ∈ Finset.univ.filter
          (fun i : Fin 2 => ∃ c ∈ A, localReg_StepWalk.Visits Mx [(Mx, C), (C, My)] c) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨c0, hc0, by rw [hAC c0 hc0]; exact Or.inr ⟨(Mx, C), by simp, rfl⟩⟩
      exact Finset.card_pos.2 ⟨0, h0⟩
  · have hE : Q.localReg2_edgeMS = ↑[(true, s(Mx, C)), (false, s(Mx, C)), (true, s(C, My)), (false, s(C, My))] := by
      unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS
      rw [Multiset.map_coe, List.map_map]
      simp [hQ, localReg2_inst_Q, SEdge.localReg2_cends, hC1, ← hMx, ← hMy, ← hC]
    have vM : localReg_StepWalk.Visits Mx [(Mx, C), (C, My)] Mx := Or.inl rfl
    have vC : localReg_StepWalk.Visits Mx [(Mx, C), (C, My)] C := Or.inr ⟨(Mx, C), by simp, rfl⟩
    have vY : localReg_StepWalk.Visits Mx [(Mx, C), (C, My)] My := Or.inr ⟨(C, My), by simp, rfl⟩
    rintro X σ ⟨s, hs, h1, h2⟩
    rw [hE] at hs
    simp only [Multiset.insert_eq_cons, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · subst h1
      rcases Sym2.mem_iff.1 h2 with rfl | rfl
      · exact ⟨0, rfl, vM⟩
      · exact ⟨0, rfl, vC⟩
    · subst h1
      rcases Sym2.mem_iff.1 h2 with rfl | rfl
      · exact ⟨1, rfl, vM⟩
      · exact ⟨1, rfl, vC⟩
    · subst h1
      rcases Sym2.mem_iff.1 h2 with rfl | rfl
      · exact ⟨0, rfl, vC⟩
      · exact ⟨0, rfl, vY⟩
    · subst h1
      rcases Sym2.mem_iff.1 h2 with rfl | rfl
      · exact ⟨1, rfl, vC⟩
      · exact ⟨1, rfl, vY⟩

/-- **Property (4) at a concrete locally standard graph** (`PathInv2.locReg345`): the graph `localReg2_inst_Q` has the coloured invariant for `p = 2`
and is locally standard, so (3), (4), (5) hold for one family of two walks; the internal molecule `{α, β}` is visited by two different walks. -/
theorem localReg2_inst_Q_locReg345 : localReg2_inst_Q.pack.LocReg345 2 :=
  PGraph.PathInv2.locReg345 localReg2_inst_Q_locStd localReg2_inst_Q_pathInv2

/-- **A negative control**: the locally standard graph `x -G- α -Ḡ- y` (the edges `G_{xα}` and `Ḡ_{yα}`, one internal vertex of neutral charge) has no
coloured family of `p = 1` walks: the one walk would have to carry both colours at the molecule `{α}` (the merged Hall invariant `PathInv` does not see this). -/
def localReg2_inst_R : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨false, false, .inl 1, .inr 0⟩]
  waved := []
  dotted := [⟨false, .inr 0, .inl 0⟩, ⟨false, .inr 0, .inl 1⟩]
  coeff := 1

theorem localReg2_inst_R_locStd : localReg2_inst_R.LocStd := by decide

theorem localReg2_inst_R_not_pathInv2 : ¬ localReg2_inst_R.pack.PathInv2 1 := by
  rintro ⟨W, col, -, -, -, hL⟩
  have hpres : ∀ σ : Bool, localReg2_present localReg2_inst_R.localReg2_edgeMS (localReg2_inst_R.molOf (Sum.inr 0)) σ := by
    intro σ
    cases σ
    · exact ⟨_, localReg2_inst_R.localReg2_mem_edgeMS (e := ⟨false, false, Sum.inl 1, Sum.inr 0⟩) (by simp [localReg2_inst_R]), rfl,
        Sym2.mem_mk_right _ _⟩
    · exact ⟨_, localReg2_inst_R.localReg2_mem_edgeMS (e := ⟨true, false, Sum.inl 0, Sum.inr 0⟩) (by simp [localReg2_inst_R]), rfl,
        Sym2.mem_mk_right _ _⟩
  obtain ⟨i, hi, -⟩ := hL _ true (hpres true)
  obtain ⟨j, hj, -⟩ := hL _ false (hpres false)
  have hij : i = j := Subsingleton.elim i j
  subst hij
  rw [hi] at hj
  exact Bool.noConfusion hj

end Instances2

end RBM.Graph
end
