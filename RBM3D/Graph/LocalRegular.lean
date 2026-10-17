/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWEdgeExp
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.ScalingOrder
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# LW-10a: `lem:localregular`, first half (T2142)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (cited `7_8:line`;
`lem:localregular`) and its proof `paper/tex/B_graphical_lemmas.tex:172-199` (cited `B:line`).
The strategy `strat_local` (`B:135-157`) and the `lvl1 lemma` are the merged `Graph/LWLvl1.lean`.
Design: T2040 (row LW-10), split by DECISIONS §42: this file is the first half; the properties (4)
and (6) of `lem:localregular` and the assembly of the lemma are LW-10b.

## Contents (namespace `RBM.Graph`; the helpers carry the prefix `localReg_`)

1. **The starting graph** `fxyPowGraph p : LGraph (Fin 2) (Fin (2 * p))` (`(eq:originGamma)`,
   `B:174-176`): `α_i = inr ⟨2i, _⟩`, `β_i = inr ⟨2i+1, _⟩`; the block `i` is
   `S_{α_iβ_i} 1_{x≠α_i} 1_{y≠α_i} Ǧ_{β_iβ_i} G_{xα_i} G_{α_iy}`, blue (`G`) for `i < p/2`, red
   (`Ḡ`) for the others (the conventions of the merged `p2Graph`).
   `fxyPowGraph_two : fxyPowGraph 2 = p2Graph` (equal, same vertex order);
   `fxyPowGraph_val_eq` (`p` even, `S` real): the value is `f_{xy}^{p/2} \overline{f_{xy}}^{p/2}`;
   `fxyPowGraph_normal`; `fxyPowGraph_counters` (`n_S = 3p`, `n_W = p`, `n_V = 2p`, `n_M = p`);
   `fxyPowGraph_ord` (`ord = p`, `(eq:initial_scaling)`, `B:201`).
2. **`(eq:MolVW)`** (`7_8:796-798`): `LGraph.molNV_le_molNW_add_one`: in a normal graph
   `n_V(𝓜) ≤ n_W(𝓜) + 1` for every molecule (a connected graph on `n` vertices has at least `n - 1`
   edges); `n_V` counts all vertices of the molecule, external ones included.
3. **The predicates (1)-(6)** of `lem:localregular` (`7_8:794-818`) on `Q : PGraph (Fin 2)` with
   `x = Q.ext 0`, `y = Q.ext 1`: `PGraph.LocReg1` ... `PGraph.LocReg6`; (3), (4), (5) refer to one
   common family `W` of `p` walks in the molecular multigraph (`LocReg3 p W`, `LocReg4 p W`,
   `LocReg5 p W`): a walk is the list of its steps `(a, b)` (a step is an edge of `molSolid`, read
   from `a` to `b`), the multiset of the steps of all walks (as unordered pairs of molecules) is
   contained in the multiset of the edges of `molSolid` (edge-disjointness), `LocReg5` is the Hall
   condition; `LocReg35 p` and `LocReg345 p` state (3)+(5) and (3)+(4)+(5) as `∃ W`.
4. **The path invariant** `PGraph.PathInv p Q` (the heart, `B:178-199`): there is a family of `p`
   walks from the molecule of `x` to that of `y`, using every edge of the molecular multigraph at
   most once (steps inside a molecule, loops, are free), with the Hall condition on the internal
   molecules.  `fxyPowGraph_pathInv`: it holds at the starting graph (each walk `x → α_i → y`
   through the molecule `{α_i, β_i}`); `pathInv_locStep`: it is preserved by every `LocStep` (for
   each output term of `(Owx)`, `(Oe1x)`, `(Oe2x)`: `localReg_pathFam_*`, then the dotted edge
   partition `LGraph.localReg_pathFam_partition`); `PGraph.PathInv.exists_walks`: it gives the
   walks of (3) and (5) (loop steps deleted).
5. **`lw_localregular_expansion`**: `lvl1_lemma_size` for `(fxyPowGraph p).pack` gives `outs`,
   `errs` with `(eq:local_Gs)` (the expectation identity of `lvl1_lemma_size`, the errors of scaling
   size `≤ W^{-D}`); every graph of `outs` satisfies (1), (2), (3), (5); every graph of
   `outs ++ errs` satisfies `PathInv`.  `lw_fxyPow_integral_eq` rewrites the left side as the
   expectation of `f_{xy}^{p/2} \overline{f_{xy}}^{p/2} = |f_{xy}|^p`.
6. Compiled instances (the last section): `fxyPowGraph 2`, `fxyPowGraph 4` (value identity,
   counters, `ord`, normality, the invariant, `(eq:MolVW)`), one `LocStep` with `pathInv_locStep`,
   the predicates, a negative control (`localReg_inst_noX_not`: the invariant fails without the
   edge `G_{xα₁}`), and `lw_localregular_expansion` at `p = 2`, `d = 3`, with the merged instance
   data of `Graph/LWWeightExp.lean`.

## How the invariant is proved

A family of walks lives on the molecules of a graph with a multiset budget of edges
(`localReg_Fam`; loop steps are free).  Three generic facts carry every step: the family is mapped
along a map `ψ` of molecules that hits every internal molecule from an internal one
(`localReg_Fam.map`); one use of an edge `{a, b}` may be rerouted through any molecule `X` as
`{a, X}, {X, b}` (`localReg_Fam.thr`); loops cost nothing (`localReg_Fam.of_add_diag`).  An
expansion term `Δ` has the solid edges `rest.map emb ++ new` (`lwSymmTwistG` of `owxExt`), where
every new vertex lies in the molecule of the vertex `x` at which the expansion is done
(`lwSymmExt_reach1/2`, the waved edges `x ~ α`, `α ~ β`): the edges removed (`p.1`, `q.1`, `q'.1`)
are either kept up to the molecule (the loops of `x`, the edges `(x, d)` moved to `(α, d)`),
merged (`R2`: `x ~ y`), or replaced by the two edges of their derivative through the molecule of
`x` (`owxDE`: `localReg_VRepl.deriv`), and `localReg_pathFam_term` turns this into the invariant
for `Δ`.  The dotted edge partition identifies vertices and drops or circles loops, which the
invariant ignores.

## Differences from the paper and the ticket (delta candidates, numbered by the dispatcher)

* `T2142a`: `(3)`-`(5)` are stated for *walks* in the molecular multigraph (each edge occurrence
  used at most once, a molecule may be revisited), not for simple paths: the proof of the paper
  replaces an edge by two edges through another molecule (`B:184-196`), which need not keep a path
  simple.  The assumption `(eq:far_ab)` (`𝓜_x ≠ 𝓜_y`, `7_8:792`) is not made: the invariant and the
  walks hold also when `𝓜_x = 𝓜_y` (closed walks); the paper's statement is the case
  `𝓜_x ≠ 𝓜_y`.
* `T2142b`: property (5) is carried by the Hall condition inside the invariant, not by the labelled
  correspondence `path ↔ molecule` of `B:178-199` (the labels are needed for (4), which is LW-10b).
* `T2142c`: `(eq:MolVW)` counts all vertices of the molecule (external ones too), which is stronger
  than counting the internal ones.
* `T2142d`: `fxyPowGraph p` and `lw_localregular_expansion` are for every `p`; evenness (`p ∈ 2ℕ`
  in the paper) is used only by `fxyPowGraph_val_eq` and `lw_fxyPow_integral_eq`.
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

/-! ## 1. Families of walks with a budget of edges (abstract)

Walks are lists of steps `(a, b)` on a type of nodes (the molecules), the budget is a multiset of unordered pairs
(the solid edges between molecules); a step that is not a loop uses one edge of the budget, a loop step is free; the Hall condition
asks that every set of internal nodes is visited by at least as many walks. -/

section Walks

variable {N : Type*}

/-- A walk given by the list of its steps: `localReg_StepWalk u v l` says that `l = [(a₁, b₁), …, (a_k, b_k)]` with
`a₁ = u`, `b_j = a_{j+1}` and `b_k = v` (the empty list is a walk from `u` to `u`). -/
def localReg_StepWalk : N → N → List (N × N) → Prop
  | u, v, [] => u = v
  | u, v, (a, b) :: l => u = a ∧ localReg_StepWalk b v l

namespace localReg_StepWalk

theorem nil (u : N) : localReg_StepWalk u u [] := rfl

theorem cons (a b v : N) (l : List (N × N)) (h : localReg_StepWalk b v l) :
    localReg_StepWalk a v ((a, b) :: l) := ⟨rfl, h⟩

theorem cons_inv {u v a b : N} {l : List (N × N)} (h : localReg_StepWalk u v ((a, b) :: l)) :
    u = a ∧ localReg_StepWalk b v l := h

theorem append {u v w : N} {l₁ l₂ : List (N × N)} (h₁ : localReg_StepWalk u v l₁) (h₂ : localReg_StepWalk v w l₂) :
    localReg_StepWalk u w (l₁ ++ l₂) := by
  induction l₁ generalizing u with
  | nil =>
    have huv : u = v := h₁
    subst huv
    simpa using h₂
  | cons st l ih =>
    obtain ⟨a, b⟩ := st
    exact ⟨h₁.1, ih h₁.2⟩

theorem append_inv {u w : N} {l₁ l₂ : List (N × N)} (h : localReg_StepWalk u w (l₁ ++ l₂)) :
    ∃ v, localReg_StepWalk u v l₁ ∧ localReg_StepWalk v w l₂ := by
  induction l₁ generalizing u with
  | nil => exact ⟨u, localReg_StepWalk.nil u, by simpa using h⟩
  | cons st l ih =>
    obtain ⟨a, b⟩ := st
    simp only [List.cons_append] at h
    obtain ⟨rfl, h'⟩ := cons_inv h
    obtain ⟨v, h1, h2⟩ := ih h'
    exact ⟨v, localReg_StepWalk.cons u b v l h1, h2⟩

theorem map {N' : Type*} (ψ : N → N') {u v : N} {l : List (N × N)} (h : localReg_StepWalk u v l) :
    localReg_StepWalk (ψ u) (ψ v) (l.map (Prod.map ψ ψ)) := by
  induction l generalizing u with
  | nil =>
    have huv : u = v := h
    subst huv
    rfl
  | cons st l ih =>
    obtain ⟨a, b⟩ := st
    exact ⟨congrArg ψ h.1, ih h.2⟩

/-- The molecules visited by a walk from `u`: its start and the ends of its steps. -/
def Visits (u : N) (l : List (N × N)) (c : N) : Prop := c = u ∨ ∃ st ∈ l, st.2 = c

theorem Visits.map {N' : Type*} (ψ : N → N') {u : N} {l : List (N × N)} {c : N} (h : Visits u l c) :
    Visits (ψ u) (l.map (Prod.map ψ ψ)) (ψ c) := by
  rcases h with h | ⟨st, hst, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨Prod.map ψ ψ st, List.mem_map_of_mem hst, by rw [← h]; rfl⟩

end localReg_StepWalk

/-- The unordered ends of the steps of a walk, as a multiset. -/
def localReg_stepEdges (l : List (N × N)) : Multiset (Sym2 N) := ((l.map fun st => s(st.1, st.2) : List (Sym2 N)) : Multiset (Sym2 N))

/-- The non-diagonal part of a multiset of unordered pairs. -/
def localReg_offDiag (m : Multiset (Sym2 N)) : Multiset (Sym2 N) := m.filter fun s => ¬ s.IsDiag

theorem localReg_offDiag_add (a b : Multiset (Sym2 N)) : localReg_offDiag (a + b) = localReg_offDiag a + localReg_offDiag b := by
  unfold localReg_offDiag; exact Multiset.filter_add _ _ _

theorem localReg_offDiag_sum {ι : Type*} (s : Finset ι) (f : ι → Multiset (Sym2 N)) :
    localReg_offDiag (∑ i ∈ s, f i) = ∑ i ∈ s, localReg_offDiag (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localReg_offDiag]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, localReg_offDiag_add, ih]

theorem localReg_stepEdges_cons (st : N × N) (l : List (N × N)) : localReg_stepEdges (st :: l) = s(st.1, st.2) ::ₘ localReg_stepEdges l := rfl

theorem localReg_stepEdges_append (l₁ l₂ : List (N × N)) : localReg_stepEdges (l₁ ++ l₂) = localReg_stepEdges l₁ + localReg_stepEdges l₂ := by
  unfold localReg_stepEdges; rw [List.map_append]; rfl

theorem localReg_stepEdges_map {N' : Type*} (ψ : N → N') (l : List (N × N)) :
    localReg_stepEdges (l.map (Prod.map ψ ψ)) = (localReg_stepEdges l).map (Sym2.map ψ) := by
  unfold localReg_stepEdges
  rw [Multiset.map_coe, List.map_map, List.map_map]
  rfl

/-- A pair is among the ends of the steps of a walk iff it is the ends of one of the steps. -/
theorem localReg_mem_stepEdges {l : List (N × N)} {t : Sym2 N} : t ∈ localReg_stepEdges l ↔ ∃ st ∈ l, s(st.1, st.2) = t := by
  unfold localReg_stepEdges; simp

/-- The walk without its loop steps. -/
def localReg_stepStrip (l : List (N × N)) : List (N × N) := l.filter fun st => decide (st.1 ≠ st.2)

/-- A walk without its loop steps is still a walk, and visits the same molecules. -/
theorem localReg_StepWalk.strip {u v : N} {l : List (N × N)} (h : localReg_StepWalk u v l) :
    localReg_StepWalk u v (localReg_stepStrip l) ∧
      ∀ c, localReg_StepWalk.Visits u l c → localReg_StepWalk.Visits u (localReg_stepStrip l) c := by
  induction l generalizing u with
  | nil =>
    refine ⟨h, fun c hc => ?_⟩
    simpa [localReg_StepWalk.Visits, localReg_stepStrip] using hc
  | cons st l ih =>
    obtain ⟨a, b⟩ := st
    obtain ⟨hua, hbv⟩ := h
    obtain ⟨ih1, ih2⟩ := ih hbv
    subst hua
    by_cases hab : u = b
    · subst hab
      have e : localReg_stepStrip ((u, u) :: l) = localReg_stepStrip l := by simp [localReg_stepStrip]
      rw [e]
      refine ⟨ih1, fun c hc => ?_⟩
      rcases hc with hc | ⟨st, hst, hc⟩
      · exact Or.inl hc
      · simp only [List.mem_cons] at hst
        rcases hst with rfl | hst
        · exact Or.inl hc.symm
        · rcases ih2 c (Or.inr ⟨st, hst, hc⟩) with h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
    · have e : localReg_stepStrip ((u, b) :: l) = (u, b) :: localReg_stepStrip l := by simp [localReg_stepStrip, hab]
      rw [e]
      refine ⟨⟨rfl, ih1⟩, fun c hc => ?_⟩
      rcases hc with hc | ⟨st, hst, hc⟩
      · exact Or.inl hc
      · simp only [List.mem_cons] at hst
        rcases hst with rfl | hst
        · exact Or.inr ⟨_, List.mem_cons_self .., hc⟩
        · rcases ih2 c (Or.inr ⟨st, hst, hc⟩) with h' | h'
          · exact Or.inr ⟨(u, b), List.mem_cons_self .., by simpa using h'.symm⟩
          · obtain ⟨st', hst', hc'⟩ := h'
            exact Or.inr ⟨st', List.mem_cons_of_mem _ hst', hc'⟩

/-- The ends of the steps of a walk without its loop steps are the non-loop part of the ends of its steps. -/
theorem localReg_stepEdges_strip (l : List (N × N)) : localReg_stepEdges (localReg_stepStrip l) = localReg_offDiag (localReg_stepEdges l) := by
  unfold localReg_stepEdges localReg_stepStrip localReg_offDiag
  rw [Multiset.filter_coe, List.filter_map]
  congr 1
  refine congrArg _ (List.filter_congr fun st _ => ?_)
  simp [Sym2.mk_isDiag_iff]

end Walks

/-! ## 2. The invariant on graphs

`LGraph.localReg_PathFam Γ p x y`: the family of walks on the molecules of `Γ` with the budget of its solid edges.  Transfer along a vertex
map (`localReg_pathFam_map`), along the dotted edge partition (`localReg_pathFam_partition`) and along one expansion term
(`localReg_pathFam_term`). -/

section GraphLevel

/-- The unordered ends of a solid edge. -/
def SEdge.localReg_ends {V : Type*} (e : SEdge V) : Sym2 V := s(e.src, e.dst)

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The unordered ends of the solid edges of a graph (weights included), with multiplicity. -/
def LGraph.localReg_endsMS (Γ : LGraph E I) : Multiset (Sym2 (E ⊕ I)) :=
  ((Γ.solid.map SEdge.localReg_ends : List (Sym2 (E ⊕ I))) : Multiset (Sym2 (E ⊕ I)))

/-- The solid edges of a graph as pairs of molecules (the edges inside a molecule give diagonal pairs). -/
def LGraph.localReg_edgeMS (Γ : LGraph E I) : Multiset (Sym2 Γ.Mol) := Γ.localReg_endsMS.map (Sym2.map Γ.molOf)

/-- A vertex map that respects the waved and `=`-dotted edges (up to molecules) induces a map of the molecules. -/
theorem LGraph.localReg_exists_molMap {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
    [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]
    (Γ : LGraph E₁ I₁) (Γ' : LGraph E₂ I₂) (φ : E₁ ⊕ I₁ → E₂ ⊕ I₂)
    (hadj : ∀ u v, Γ.adj u v = true → Γ'.molGraph.Reachable (φ u) (φ v)) :
    ∃ ψ : Γ.Mol → Γ'.Mol, ∀ v, ψ (Γ.molOf v) = Γ'.molOf (φ v) := by
  have hwalk : ∀ {v w : E₁ ⊕ I₁} (p : Γ.molGraph.Walk v w), Γ'.molGraph.Reachable (φ v) (φ w) := by
    intro v w p
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact (hadj _ _ ((owx_molGraph_adj Γ _ _).1 h).2).trans ih
  exact ⟨SimpleGraph.ConnectedComponent.lift (fun v => Γ'.molOf (φ v))
    (fun _ _ p _ => SimpleGraph.ConnectedComponent.eq.2 (hwalk p)), fun v => rfl⟩

/-- The twist `(c, t)` does not change the molecules. -/
theorem localReg_lwSymmTwistG_molGraph (c t : Bool) (Γ : LGraph E I) : (lwSymmTwistG c t Γ).molGraph = Γ.molGraph := by
  unfold LGraph.molGraph
  rw [lwSymmTwistG_adj]

local macro "localReg_msnorm" : tactic => `(tactic| (simp only [SEdge.localReg_ends_mk, SEdge.localReg_ends_map, Sym2.map_mk, lwSymmTwistP, List.map_cons, List.map_nil,
  Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe, Multiset.coe_nil,
  Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq]; try abel))

local macro "localReg_msnormx" : tactic => `(tactic| (simp only [SEdge.localReg_ends_mk, SEdge.localReg_ends_map, Sym2.map_mk, lwSymmTwistP, List.map_cons, List.map_nil,
  Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe, Multiset.coe_nil,
  Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq]; try abel))

/-! ## 3. The terms of the three expansions

One lemma for each output term of `(Owx)`, `(Oe1x)`, `(Oe2x)` (the twisted `owxExt` terms of `Graph/LWSymm.lean`): the edges removed and the
edges added, read in the molecules (the new vertices lie in the molecule of `x`), and the replacement of the former by the latter
(`localReg_VRepl`). -/

section Terms

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The frame of a selected edge has the molecules (the adjacency) of the graph. -/
theorem localReg_lwSymmFrame_adj (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).adj = Γ.adj := lwSymmTwistG_adj c t (lwSymmUncirc Γ p)

/-- The frame of two selected edges has the molecules (the adjacency) of the graph. -/
theorem localReg_lwSymmFrame2_adj (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).adj = Γ.adj := lwSymmTwistG_adj c t (lwSymmUncirc2 Γ p q)

/-- the perm of the solid edges for the two selected edges -/
theorem localReg_lwSplit_perm2 (l : List (SEdge (E ⊕ I))) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit l)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) : l.Perm (p.1 :: q.1 :: q.2) :=
  (lwSplit_perm l p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)

/-- The two ends of a waved edge lie in one molecule. -/
theorem LGraph.localReg_reach_of_waved (Γ : LGraph E I) (e : WEdge (E ⊕ I)) (he : e ∈ Γ.waved) :
    Γ.molGraph.Reachable e.x e.y := by
  by_cases hne : e.x = e.y
  · rw [hne]
  · refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨hne, ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- The solid edges of a graph with three selected edges `p.1`, `q.1`, `q'.1` (`lwSplit` three times). -/
theorem localReg_lwSplit_perm3 (l : List (SEdge (E ⊕ I))) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit l)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq' : q' ∈ lwSplit q.2) : l.Perm (p.1 :: q.1 :: q'.1 :: q'.2) :=
  (localReg_lwSplit_perm2 l p hp q hq).trans (((lwSplit_perm q.2 q' hq').cons q.1).cons p.1)

end Terms

end GraphLevel


/-! ## 4. The starting graph `|f_{xy}(G)|^p` (`(eq:originGamma)`, `B:174-176`) -/

/-- the vertex `α_i` of the block `i` -/
def localReg_fxyAlpha {p : ℕ} (i : Fin p) : Fin (2 * p) := ⟨2 * i.1, by omega⟩
/-- the vertex `β_i` of the block `i` -/
def localReg_fxyBeta {p : ℕ} (i : Fin p) : Fin (2 * p) := ⟨2 * i.1 + 1, by omega⟩

/-- the three solid edges of the block `i`: the light-weight `Ǧ_{β_iβ_i}`, `G_{xα_i}`, `G_{α_iy}` (blue for `i < p/2`, red otherwise) -/
def localReg_fxyBlock (p : ℕ) (i : Fin p) : List (SEdge (Fin 2 ⊕ Fin (2 * p))) :=
  [⟨decide (i.1 < p / 2), true, .inr (localReg_fxyBeta i), .inr (localReg_fxyBeta i)⟩,
   ⟨decide (i.1 < p / 2), false, .inl 0, .inr (localReg_fxyAlpha i)⟩,
   ⟨decide (i.1 < p / 2), false, .inr (localReg_fxyAlpha i), .inl 1⟩]

/-- **The starting graph `|f_{xy}(G)|^p`** (`(eq:originGamma)`, `B:174-176`; `p ∈ 2ℕ` in the paper): the external vertices are `x = inl 0`, `y = inl 1`, the internal ones `α_i = inr ⟨2i, _⟩`, `β_i = inr ⟨2i+1, _⟩`; each block `i` has the solid edges `Ǧ_{β_iβ_i}` (a circled loop), `G_{xα_i}`, `G_{α_iy}` (blue for `i < p/2`, red `Ḡ` otherwise), the waved edge `S_{α_iβ_i}` and the `×`-dotted edges `1_{α_i≠x}`, `1_{α_i≠y}`; the coefficient is `1`. -/
def fxyPowGraph (p : ℕ) : LGraph (Fin 2) (Fin (2 * p)) where
  solid := (List.finRange p).flatMap (localReg_fxyBlock p)
  waved := (List.finRange p).map fun i => ⟨false, true, .inr (localReg_fxyAlpha i), .inr (localReg_fxyBeta i)⟩
  dotted := (List.finRange p).flatMap fun i => [⟨false, .inr (localReg_fxyAlpha i), .inl 0⟩, ⟨false, .inr (localReg_fxyAlpha i), .inl 1⟩]
  coeff := 1

/-- The vertices `α_i` are distinct. -/
theorem localReg_fxyAlpha_inj {p : ℕ} {i j : Fin p} (h : localReg_fxyAlpha i = localReg_fxyAlpha j) : i = j := by
  have := congrArg Fin.val h
  simp only [localReg_fxyAlpha] at this
  exact Fin.ext (by omega)

/-- `α_i ≠ β_j`. -/
theorem localReg_fxyAlpha_ne_beta {p : ℕ} (i j : Fin p) : localReg_fxyAlpha i ≠ localReg_fxyBeta j := by
  intro h
  have := congrArg Fin.val h
  simp only [localReg_fxyAlpha, localReg_fxyBeta] at this
  omega

/-- The vertices `β_i` are distinct. -/
theorem localReg_fxyBeta_inj {p : ℕ} {i j : Fin p} (h : localReg_fxyBeta i = localReg_fxyBeta j) : i = j := by
  have := congrArg Fin.val h
  simp only [localReg_fxyBeta] at this
  exact Fin.ext (by omega)

/-- The solid edges of the starting graph are those of the blocks. -/
theorem localReg_fxy_mem_solid {p : ℕ} (e : SEdge (Fin 2 ⊕ Fin (2 * p))) :
    e ∈ (fxyPowGraph p).solid ↔ ∃ i : Fin p, e ∈ localReg_fxyBlock p i := by
  simp [fxyPowGraph]

/-- The waved edges of the starting graph are `S_{α_iβ_i}`. -/
theorem localReg_fxy_mem_waved {p : ℕ} (e : WEdge (Fin 2 ⊕ Fin (2 * p))) :
    e ∈ (fxyPowGraph p).waved ↔ ∃ i : Fin p, e = ⟨false, true, .inr (localReg_fxyAlpha i), .inr (localReg_fxyBeta i)⟩ := by
  simp [fxyPowGraph, eq_comm]

/-- The dotted edges of the starting graph are the `×`-dotted edges `1_{α_i≠x}`, `1_{α_i≠y}`. -/
theorem localReg_fxy_mem_dotted {p : ℕ} (e : DEdge (Fin 2 ⊕ Fin (2 * p))) :
    e ∈ (fxyPowGraph p).dotted ↔ ∃ i : Fin p, e = ⟨false, .inr (localReg_fxyAlpha i), .inl 0⟩ ∨ e = ⟨false, .inr (localReg_fxyAlpha i), .inl 1⟩ := by
  simp [fxyPowGraph]

/-- The counters `n_S`, `n_W`, `n_V` of the starting graph. -/
theorem localReg_fxyPowGraph_counters_aux (p : ℕ) :
    (fxyPowGraph p).nS = 3 * p ∧ (fxyPowGraph p).nW = p ∧ (fxyPowGraph p).nV = 2 * p := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LGraph.nS, fxyPowGraph, List.length_flatMap, localReg_fxyBlock]
    omega
  · simp [LGraph.nW, fxyPowGraph]
  · simp [LGraph.nV]


/-- The pairs joined by a solid non-loop edge in the starting graph: `{x, α_i}`, `{α_i, y}`. -/
theorem localReg_fxy_sbetween_iff {p : ℕ} (u v : Fin 2 ⊕ Fin (2 * p)) :
    (fxyPowGraph p).SBetween u v ↔ ∃ i : Fin p, (u = .inr (localReg_fxyAlpha i) ∧ (v = .inl 0 ∨ v = .inl 1)) ∨
      (v = .inr (localReg_fxyAlpha i) ∧ (u = .inl 0 ∨ u = .inl 1)) := by
  constructor
  · rintro ⟨e, he, hne, h⟩
    obtain ⟨i, hi⟩ := (localReg_fxy_mem_solid e).1 he
    simp only [localReg_fxyBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    refine ⟨i, ?_⟩
    rcases hi with rfl | rfl | rfl
    · exact absurd rfl hne
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; exact ⟨h2.symm, Or.inl h1.symm⟩
      · left; exact ⟨h2.symm, Or.inl h1.symm⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1.symm, Or.inr h2.symm⟩
      · right; exact ⟨h1.symm, Or.inr h2.symm⟩
  · rintro ⟨i, ⟨hu, hv | hv⟩ | ⟨hv, hu | hu⟩⟩
    · refine ⟨⟨decide (i.1 < p / 2), false, .inl 0, .inr (localReg_fxyAlpha i)⟩, (localReg_fxy_mem_solid _).2 ⟨i, by simp [localReg_fxyBlock]⟩, by simp, ?_⟩
      right; exact ⟨hv.symm, hu.symm⟩
    · refine ⟨⟨decide (i.1 < p / 2), false, .inr (localReg_fxyAlpha i), .inl 1⟩, (localReg_fxy_mem_solid _).2 ⟨i, by simp [localReg_fxyBlock]⟩, by simp, ?_⟩
      left; exact ⟨hu.symm, hv.symm⟩
    · refine ⟨⟨decide (i.1 < p / 2), false, .inl 0, .inr (localReg_fxyAlpha i)⟩, (localReg_fxy_mem_solid _).2 ⟨i, by simp [localReg_fxyBlock]⟩, by simp, ?_⟩
      left; exact ⟨hu.symm, hv.symm⟩
    · refine ⟨⟨decide (i.1 < p / 2), false, .inr (localReg_fxyAlpha i), .inl 1⟩, (localReg_fxy_mem_solid _).2 ⟨i, by simp [localReg_fxyBlock]⟩, by simp, ?_⟩
      right; exact ⟨hv.symm, hu.symm⟩

/-- The pairs joined by a `×`-dotted edge in the starting graph: `{x, α_i}`, `{α_i, y}`. -/
theorem localReg_fxy_xbetween_iff {p : ℕ} (u v : Fin 2 ⊕ Fin (2 * p)) :
    (fxyPowGraph p).XBetween u v ↔ ∃ i : Fin p, (u = .inr (localReg_fxyAlpha i) ∧ (v = .inl 0 ∨ v = .inl 1)) ∨
      (v = .inr (localReg_fxyAlpha i) ∧ (u = .inl 0 ∨ u = .inl 1)) := by
  constructor
  · rintro ⟨e, he, -, h⟩
    obtain ⟨i, hi⟩ := (localReg_fxy_mem_dotted e).1 he
    refine ⟨i, ?_⟩
    rcases hi with rfl | rfl
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1.symm, Or.inl h2.symm⟩
      · right; exact ⟨h1.symm, Or.inl h2.symm⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1.symm, Or.inr h2.symm⟩
      · right; exact ⟨h1.symm, Or.inr h2.symm⟩
  · rintro ⟨i, ⟨hu, hv | hv⟩ | ⟨hv, hu | hu⟩⟩
    · refine ⟨⟨false, .inr (localReg_fxyAlpha i), .inl 0⟩, (localReg_fxy_mem_dotted _).2 ⟨i, Or.inl rfl⟩, rfl, ?_⟩
      left; exact ⟨hu.symm, hv.symm⟩
    · refine ⟨⟨false, .inr (localReg_fxyAlpha i), .inl 1⟩, (localReg_fxy_mem_dotted _).2 ⟨i, Or.inr rfl⟩, rfl, ?_⟩
      left; exact ⟨hu.symm, hv.symm⟩
    · refine ⟨⟨false, .inr (localReg_fxyAlpha i), .inl 0⟩, (localReg_fxy_mem_dotted _).2 ⟨i, Or.inl rfl⟩, rfl, ?_⟩
      right; exact ⟨hv.symm, hu.symm⟩
    · refine ⟨⟨false, .inr (localReg_fxyAlpha i), .inl 1⟩, (localReg_fxy_mem_dotted _).2 ⟨i, Or.inr rfl⟩, rfl, ?_⟩
      right; exact ⟨hv.symm, hu.symm⟩

/-- **The starting graph is normal** (`defnlvl0`). -/
theorem fxyPowGraph_normal (p : ℕ) : (fxyPowGraph p).Normal := by
  refine ⟨?_, fun u v _ => ?_, ?_⟩
  · intro e he
    obtain ⟨i, rfl | rfl⟩ := (localReg_fxy_mem_dotted e).1 he <;> rfl
  · rw [localReg_fxy_xbetween_iff, localReg_fxy_sbetween_iff]
  · intro e he hl
    obtain ⟨i, hi⟩ := (localReg_fxy_mem_solid e).1 he
    simp only [localReg_fxyBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rfl
    · exact absurd hl (by simp)
    · exact absurd hl (by simp)


/-- the block of a vertex: an external vertex is its own block, `α_i` and `β_i` form the block `i` -/
def localReg_fxyBlk {p : ℕ} : Fin 2 ⊕ Fin (2 * p) → Fin 2 ⊕ Fin p
  | .inl a => .inl a
  | .inr k => .inr ⟨k.1 / 2, by omega⟩

/-- The adjacency of the starting graph (waved edges only): `α_i ~ β_i`. -/
theorem localReg_fxy_adj_iff {p : ℕ} (u v : Fin 2 ⊕ Fin (2 * p)) :
    (fxyPowGraph p).adj u v = true ↔ ∃ i : Fin p,
      (u = .inr (localReg_fxyAlpha i) ∧ v = .inr (localReg_fxyBeta i)) ∨ (v = .inr (localReg_fxyAlpha i) ∧ u = .inr (localReg_fxyBeta i)) := by
  simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (⟨e, he, h⟩ | ⟨e, he, h1, h⟩)
    · obtain ⟨i, rfl⟩ := (localReg_fxy_mem_waved e).1 he
      refine ⟨i, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1.symm, h2.symm⟩
      · right; exact ⟨h1.symm, h2.symm⟩
    · obtain ⟨i, rfl | rfl⟩ := (localReg_fxy_mem_dotted e).1 he <;> simp at h1
  · rintro ⟨i, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · left; exact ⟨_, (localReg_fxy_mem_waved _).2 ⟨i, rfl⟩, Or.inl ⟨hu.symm, hv.symm⟩⟩
    · left; exact ⟨_, (localReg_fxy_mem_waved _).2 ⟨i, rfl⟩, Or.inr ⟨hv.symm, hu.symm⟩⟩

/-- The block of `α_i` is `i`. -/
theorem localReg_fxy_blk_alpha {p : ℕ} (i : Fin p) : localReg_fxyBlk (Sum.inr (localReg_fxyAlpha i) : Fin 2 ⊕ Fin (2 * p)) = Sum.inr i := by
  simp only [localReg_fxyBlk, localReg_fxyAlpha]
  exact congrArg Sum.inr (Fin.ext (by simp))

/-- The block of `β_i` is `i`. -/
theorem localReg_fxy_blk_beta {p : ℕ} (i : Fin p) : localReg_fxyBlk (Sum.inr (localReg_fxyBeta i) : Fin 2 ⊕ Fin (2 * p)) = Sum.inr i := by
  simp only [localReg_fxyBlk, localReg_fxyBeta]
  exact congrArg Sum.inr (Fin.ext (by simp; omega))

/-- Vertices in one molecule of the starting graph are in one block. -/
theorem localReg_fxy_reach_blk {p : ℕ} {u v : Fin 2 ⊕ Fin (2 * p)} (h : (fxyPowGraph p).molGraph.Reachable u v) :
    localReg_fxyBlk u = localReg_fxyBlk v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons h _ ih =>
    rw [← ih]
    obtain ⟨-, hadj⟩ := (owx_molGraph_adj _ _ _).1 h
    obtain ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (localReg_fxy_adj_iff _ _).1 hadj
    · rw [localReg_fxy_blk_alpha, localReg_fxy_blk_beta]
    · rw [localReg_fxy_blk_alpha, localReg_fxy_blk_beta]

/-- Vertices in one block of the starting graph are in one molecule. -/
theorem localReg_fxy_reach_of_blk {p : ℕ} {u v : Fin 2 ⊕ Fin (2 * p)} (h : localReg_fxyBlk u = localReg_fxyBlk v) :
    (fxyPowGraph p).molGraph.Reachable u v := by
  have key : ∀ k : Fin (2 * p), (fxyPowGraph p).molGraph.Reachable (Sum.inr k) (Sum.inr (localReg_fxyAlpha ⟨k.1 / 2, by omega⟩)) := by
    intro k
    by_cases hk : k.1 % 2 = 0
    · have hk' : (Sum.inr k : Fin 2 ⊕ Fin (2 * p)) = Sum.inr (localReg_fxyAlpha ⟨k.1 / 2, by omega⟩) :=
        congrArg Sum.inr (Fin.ext (by simp [localReg_fxyAlpha]; omega))
      rw [hk']
    · have hk' : (Sum.inr k : Fin 2 ⊕ Fin (2 * p)) = Sum.inr (localReg_fxyBeta ⟨k.1 / 2, by omega⟩) :=
        congrArg Sum.inr (Fin.ext (by simp [localReg_fxyBeta]; omega))
      rw [hk']
      refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨fun h => localReg_fxyAlpha_ne_beta _ _ (Sum.inr_injective h).symm, (localReg_fxy_adj_iff _ _).2 ⟨_, Or.inr ⟨rfl, rfl⟩⟩⟩)
  rcases u with a | k <;> rcases v with a' | k'
  · simp only [localReg_fxyBlk, Sum.inl.injEq] at h
    rw [h]
  · simp [localReg_fxyBlk] at h
  · simp [localReg_fxyBlk] at h
  · simp only [localReg_fxyBlk, Sum.inr.injEq, Fin.mk.injEq] at h
    refine (key k).trans (Eq.mpr ?_ (key k').symm)
    rw [show (⟨k.1 / 2, by omega⟩ : Fin p) = ⟨k'.1 / 2, by omega⟩ from Fin.ext h]

/-- Two vertices of the starting graph are in one molecule iff they are in one block. -/
theorem localReg_fxy_molOf_eq_iff {p : ℕ} (u v : Fin 2 ⊕ Fin (2 * p)) :
    (fxyPowGraph p).molOf u = (fxyPowGraph p).molOf v ↔ localReg_fxyBlk u = localReg_fxyBlk v :=
  ⟨fun h => localReg_fxy_reach_blk (SimpleGraph.ConnectedComponent.eq.1 h),
    fun h => SimpleGraph.ConnectedComponent.eq.2 (localReg_fxy_reach_of_blk h)⟩


/-- the molecule of the block `i` -/
def localReg_fxyMol {p : ℕ} (i : Fin p) : (fxyPowGraph p).Mol := (fxyPowGraph p).molOf (Sum.inr (localReg_fxyAlpha i))

/-- The molecules `{α_i, β_i}` are distinct. -/
theorem localReg_fxyMol_inj {p : ℕ} {i j : Fin p} (h : localReg_fxyMol i = localReg_fxyMol j) : i = j := by
  have := (localReg_fxy_molOf_eq_iff _ _).1 h
  rw [localReg_fxy_blk_alpha, localReg_fxy_blk_alpha] at this
  exact Sum.inr_injective this

/-- The molecule of a block is internal. -/
theorem localReg_fxyMol_internal {p : ℕ} (i : Fin p) : ¬ (fxyPowGraph p).IsExtMol (localReg_fxyMol i) := by
  rintro ⟨a, ha⟩
  have := (localReg_fxy_molOf_eq_iff _ _).1 ha
  rw [localReg_fxy_blk_alpha] at this
  simp [localReg_fxyBlk] at this

/-- Every internal molecule of the starting graph is a block. -/
theorem localReg_fxy_internal_eq {p : ℕ} (c : (fxyPowGraph p).Mol) (hc : ∀ a : Fin 2, (fxyPowGraph p).molOf (Sum.inl a) ≠ c) :
    ∃ i : Fin p, c = localReg_fxyMol i := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    rcases v with a | k
    · exact absurd rfl (hc a)
    · refine ⟨⟨k.1 / 2, by omega⟩, ?_⟩
      exact (localReg_fxy_molOf_eq_iff (Sum.inr k) (Sum.inr (localReg_fxyAlpha ⟨k.1 / 2, by omega⟩))).2 (by rw [localReg_fxy_blk_alpha]; rfl)

/-- `n_M(Γ_p) = p`: the internal molecules of the starting graph are the `p` blocks `{α_i, β_i}`. -/
theorem fxyPowGraph_nM (p : ℕ) : (fxyPowGraph p).nM = p := by
  rw [LGraph.nM_eq_card]
  have e : Fin p ≃ {c : (fxyPowGraph p).Mol // ¬ (fxyPowGraph p).IsExtMol c} :=
    Equiv.ofBijective (fun i => ⟨localReg_fxyMol i, localReg_fxyMol_internal i⟩)
      ⟨fun i j h => localReg_fxyMol_inj (congrArg Subtype.val h),
        fun c => by obtain ⟨i, hi⟩ := localReg_fxy_internal_eq c.1 (fun a ha => c.2 ⟨a, ha⟩); exact ⟨i, Subtype.ext hi.symm⟩⟩
  rw [← Nat.card_congr e]
  simp

/-- The multiset of a `flatMap` is the sum of the multisets of the pieces. -/
theorem localReg_coe_flatMap_eq_sum {α β : Type*} (L : List α) (F : α → List β) :
    ((L.flatMap F : List β) : Multiset β) = (L.map fun a => (F a : Multiset β)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih, ← Multiset.coe_add]

/-- the equivalence between labellings of the `2p` internal vertices and of the `p` pairs `(α_i, β_i)` -/
def localReg_fxyPairEquiv {ι : Type*} (p : ℕ) : (Fin (2 * p) → ι) ≃ (Fin p → ι × ι) where
  toFun ℓ i := (ℓ (localReg_fxyAlpha i), ℓ (localReg_fxyBeta i))
  invFun f k := if k.1 % 2 = 0 then (f ⟨k.1 / 2, by omega⟩).1 else (f ⟨k.1 / 2, by omega⟩).2
  left_inv ℓ := by
    funext k
    by_cases hk : k.1 % 2 = 0
    · simp only [hk, ↓reduceIte]
      congr 1
      exact Fin.ext (by simp [localReg_fxyAlpha]; omega)
    · simp only [hk, ↓reduceIte]
      congr 1
      exact Fin.ext (by simp [localReg_fxyBeta]; omega)
  right_inv f := by
    funext i
    simp only [localReg_fxyAlpha, localReg_fxyBeta]
    have h0 : (2 * i.1) % 2 = 0 := by omega
    have h1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
    have hi0 : (⟨(2 * i.1) / 2, by omega⟩ : Fin p) = i := Fin.ext (by simp)
    have hi1 : (⟨(2 * i.1 + 1) / 2, by omega⟩ : Fin p) = i := Fin.ext (by simp; omega)
    refine Prod.ext ?_ ?_
    · simp only [h0, ↓reduceIte, hi0]
    · simp only [h1, ↓reduceIte, hi1]

/-- The labelling of `α_i` by the inverse of the pairing equivalence. -/
theorem localReg_fxyPairEquiv_symm_alpha {ι : Type*} {p : ℕ} (f : Fin p → ι × ι) (i : Fin p) :
    (localReg_fxyPairEquiv p).symm f (localReg_fxyAlpha i) = (f i).1 := by
  have h0 : (2 * i.1) % 2 = 0 := by omega
  have hi0 : (⟨(2 * i.1) / 2, by omega⟩ : Fin p) = i := Fin.ext (by simp)
  simp only [localReg_fxyPairEquiv, localReg_fxyAlpha, Equiv.coe_fn_symm_mk, h0, ↓reduceIte, hi0]

/-- The labelling of `β_i` by the inverse of the pairing equivalence. -/
theorem localReg_fxyPairEquiv_symm_beta {ι : Type*} {p : ℕ} (f : Fin p → ι × ι) (i : Fin p) :
    (localReg_fxyPairEquiv p).symm f (localReg_fxyBeta i) = (f i).2 := by
  have h1 : (2 * i.1 + 1) % 2 ≠ 0 := by omega
  have hi1 : (⟨(2 * i.1 + 1) / 2, by omega⟩ : Fin p) = i := Fin.ext (by simp; omega)
  simp only [localReg_fxyPairEquiv, localReg_fxyBeta, Equiv.coe_fn_symm_mk, h1, ↓reduceIte, hi1]

/-- A sum over the labellings of the `2p` internal vertices of a product over the `p` pairs `(α_i, β_i)` factorises. -/
theorem localReg_fxy_sum_pairs {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (F : Fin p → ι → ι → ℂ) :
    ∑ ℓ : Fin (2 * p) → ι, ∏ i : Fin p, F i (ℓ (localReg_fxyAlpha i)) (ℓ (localReg_fxyBeta i)) = ∏ i : Fin p, ∑ a, ∑ b, F i a b := by
  rw [← (localReg_fxyPairEquiv p).symm.sum_comp]
  simp only [localReg_fxyPairEquiv_symm_alpha, localReg_fxyPairEquiv_symm_beta]
  have := Finset.prod_univ_sum (fun _ : Fin p => (Finset.univ : Finset (ι × ι))) (fun i c => F i c.1 c.2)
  simp only [Fintype.piFinset_univ] at this
  rw [← Finset.prod_congr rfl fun i _ => (Fintype.sum_prod_type (fun c : ι × ι => F i c.1 c.2)).symm] at *
  simpa using this.symm


/-- The product over a `flatMap` is the product of the products of the pieces. -/
theorem localReg_fxy_prod_flatMap {α β : Type*} (L : List α) (F : α → List β) (g : β → ℂ) :
    ((L.flatMap F).map g).prod = (L.map fun a => ((F a).map g).prod).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-! ## 5. The value identity -/

section Value

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the value of the block `i` (colour `σ`) at the labels `a = ℓ(α_i)`, `b = ℓ(β_i)` of its internal vertices and the external labels `x`, `y` -/
def localReg_fxyBlockVal (D : LData ι) (x y : ι) (σ : Bool) (a b : ι) : ℂ :=
  (if σ then (D.G b b - D.M b b) * (D.G x a * D.G a y) else star ((D.G b b - D.M b b) * (D.G x a * D.G a y))) *
    D.S a b * ((if a = x then 0 else 1) * (if a = y then 0 else 1))

/-- The term of the starting graph at a labelling is the product over the blocks. -/
theorem localReg_fxy_term (D : LData ι) (p : ℕ) (x y : ι) (ℓi : Fin (2 * p) → ι) :
    (fxyPowGraph p).term D (Sum.elim ![x, y] ℓi) =
      ∏ i : Fin p, localReg_fxyBlockVal D x y (decide (i.1 < p / 2)) (ℓi (localReg_fxyAlpha i)) (ℓi (localReg_fxyBeta i)) := by
  unfold LGraph.term
  have hc : (fxyPowGraph p).coeff = 1 := rfl
  have hs : (fxyPowGraph p).solid = (List.finRange p).flatMap (localReg_fxyBlock p) := rfl
  have hw : (fxyPowGraph p).waved = (List.finRange p).map fun i => (⟨false, true, .inr (localReg_fxyAlpha i), .inr (localReg_fxyBeta i)⟩ : WEdge (Fin 2 ⊕ Fin (2 * p))) := rfl
  have hd : (fxyPowGraph p).dotted = (List.finRange p).flatMap fun i => [(⟨false, .inr (localReg_fxyAlpha i), .inl 0⟩ : DEdge (Fin 2 ⊕ Fin (2 * p))), ⟨false, .inr (localReg_fxyAlpha i), .inl 1⟩] := rfl
  rw [hc, hs, hw, hd, one_mul, localReg_fxy_prod_flatMap, localReg_fxy_prod_flatMap, List.map_map]
  simp only [← Fin.prod_univ_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [localReg_fxyBlock, SEdge.val, WEdge.val, DEdge.val, localReg_fxyBlockVal, Function.comp_apply, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Sum.elim_inl, Sum.elim_inr]
  by_cases hσ : decide (i.1 < p / 2) = true
  · simp only [hσ, ite_true, Bool.false_eq_true, ite_false, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      iff_false, mul_one, ite_not]
    try ring
  · simp only [hσ, ite_true, Bool.false_eq_true, ite_false, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      iff_false, mul_one, ite_not, star_mul', star_sub]
    try ring


/-- The sum over the labels of a blue block is `f_{xy}`. -/
theorem localReg_fxy_blockSum_blue (D : LData ι) (x y : ι) : ∑ a, ∑ b, localReg_fxyBlockVal D x y true a b = fxyVal D x y := by
  unfold fxyVal localReg_fxyBlockVal
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a = x ∨ a = y
  · rcases h with rfl | rfl <;> simp
  · push Not at h
    simp only [h.1, h.2, ite_false, ↓reduceIte, ite_true, mul_one, not_false_eq_true, or_self]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

/-- The sum over the labels of a red block is `\overline{f_{xy}}` (`S` real). -/
theorem localReg_fxy_blockSum_red (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (x y : ι) :
    ∑ a, ∑ b, localReg_fxyBlockVal D x y false a b = star (fxyVal D x y) := by
  unfold fxyVal localReg_fxyBlockVal
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a = x ∨ a = y
  · rcases h with rfl | rfl <;> simp
  · push Not at h
    simp only [h.1, h.2, ite_false, ↓reduceIte, mul_one, not_false_eq_true, or_self, Bool.false_eq_true]
    rw [star_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [star_mul', hS]
    ring

/-- **The value of the starting graph is `|f_{xy}|^p`** (`(eq:originGamma)`, `B:174-176`; `S` real, `p` even): the graph factorises over the
`p` blocks `(α_i, β_i)`, `p/2` blue ones (`f_{xy}`) and `p/2` red ones (`\overline{f_{xy}}`). -/
theorem fxyPowGraph_val_eq (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (p : ℕ) (hp : Even p) (x y : ι) :
    (fxyPowGraph p).val D ![x, y] = fxyVal D x y ^ (p / 2) * star (fxyVal D x y) ^ (p / 2) := by
  unfold LGraph.val
  simp only [localReg_fxy_term]
  rw [localReg_fxy_sum_pairs p (fun i a b => localReg_fxyBlockVal D x y (decide (i.1 < p / 2)) a b)]
  have hb : ∀ i : Fin p, ∑ a, ∑ b, localReg_fxyBlockVal D x y (decide (i.1 < p / 2)) a b =
      if i.1 < p / 2 then fxyVal D x y else star (fxyVal D x y) := by
    intro i
    by_cases h : i.1 < p / 2
    · simp [h, localReg_fxy_blockSum_blue]
    · simp [h, localReg_fxy_blockSum_red D hS]
  simp only [hb]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter fun i : Fin p => i.1 < p / 2).card = p / 2 := by
    rw [Fin.card_filter_val_lt]; omega
  have h2 : (Finset.univ.filter fun i : Fin p => ¬ i.1 < p / 2).card = p / 2 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p))) (fun i : Fin p => i.1 < p / 2)
    rw [Finset.card_univ, Fintype.card_fin, h1] at this
    obtain ⟨r, hr⟩ := hp
    omega
  rw [h1, h2]

end Value


/-! ## 6. `(eq:MolVW)` -/

section MolVW

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `n_V(𝓜)`: the number of vertices (internal and external) of the molecule `c` -/
def LGraph.molNV (Γ : LGraph E I) (c : Γ.Mol) : ℕ := (Finset.univ.filter fun v : E ⊕ I => Γ.molOf v = c).card

/-- `n_W(𝓜)`: the number of waved edges of the molecule `c` (a waved edge lies inside the molecule of its ends) -/
def LGraph.molNW (Γ : LGraph E I) (c : Γ.Mol) : ℕ := (Γ.waved.filter fun e => Γ.molOf e.x = c).length

/-- **`(eq:MolVW)`** (`7_8:798`, `B:178`): in a normal graph (no `=`-dotted edges) the vertices of a molecule are connected by its waved edges, so
`n_V(𝓜) ≤ n_W(𝓜) + 1` (a connected graph on `n` vertices has at least `n - 1` edges). -/
theorem LGraph.molNV_le_molNW_add_one (Γ : LGraph E I) (hN : Γ.Normal) (c : Γ.Mol) :
    Γ.molNV c ≤ Γ.molNW c + 1 := by
  have hconn := c.connected_toSimpleGraph
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card ↥c = Γ.molNV c := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    unfold LGraph.molNV
    congr 1
  set L : List (WEdge (E ⊕ I)) := Γ.waved.filter fun e => Γ.molOf e.x = c with hL
  have hsub : ∀ e : c.toSimpleGraph.edgeSet, Sym2.map Subtype.val e.1 ∈ (L.map fun e => s(e.x, e.y)).toFinset := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h u v =>
      have hadj : c.toSimpleGraph.Adj u v := he
      have hadj' : Γ.molGraph.Adj u.1 v.1 := hadj
      obtain ⟨-, hadj2⟩ := (owx_molGraph_adj _ _ _).1 hadj'
      simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hadj2
      rcases hadj2 with ⟨e', he', h'⟩ | ⟨e', he', h1, -⟩
      · simp only [List.mem_toFinset, List.mem_map, Sym2.map_mk]
        refine ⟨e', List.mem_filter.2 ⟨he', ?_⟩, ?_⟩
        · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [decide_eq_true_iff, h1]; exact u.2
          · rw [decide_eq_true_iff, h1]; exact v.2
        · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2]; exact Sym2.eq_swap
      · exact absurd h1 (by simp [hN.1 e' he'])
  let g : c.toSimpleGraph.edgeSet → ↥((L.map fun e => s(e.x, e.y)).toFinset) :=
    fun e => ⟨Sym2.map Subtype.val e.1, hsub e⟩
  have hg : Function.Injective g := by
    intro e₁ e₂ h
    exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
  have h2 : Nat.card c.toSimpleGraph.edgeSet ≤ L.length := by
    refine (Nat.card_le_card_of_injective g hg).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (List.toFinset_card_le _).trans (by simp)
  have : Γ.molNW c = L.length := rfl
  omega

end MolVW



/-! ## 7. The invariant along a `LocStep` -/

/-! ## 8. The predicates (1)-(6) of `lem:localregular` and the walks -/

section Predicates

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The solid edges between different molecules, as unordered pairs of molecules: the edges of the molecular graph (`molSolid`). -/
def LGraph.localReg_molEdgeMS (Γ : LGraph E I) : Multiset (Sym2 Γ.Mol) :=
  ((Γ.molSolid.map fun e => s(e.src, e.dst) : List (Sym2 Γ.Mol)) : Multiset (Sym2 Γ.Mol))

/-- The non-loop part of the molecular edges is `molSolid` read as unordered pairs. -/
theorem LGraph.localReg_offDiag_edgeMS (Γ : LGraph E I) : localReg_offDiag Γ.localReg_edgeMS = Γ.localReg_molEdgeMS := by
  unfold localReg_offDiag LGraph.localReg_edgeMS LGraph.localReg_endsMS LGraph.localReg_molEdgeMS LGraph.molSolid
  rw [Multiset.map_coe, List.map_map, Multiset.filter_coe, List.filter_map, List.map_map]
  have hf : (Sym2.map Γ.molOf ∘ SEdge.localReg_ends) = ((fun e : SEdge Γ.Mol => s(e.src, e.dst)) ∘ SEdge.map Γ.molOf) := by
    funext e; rfl
  rw [hf]
  have hp : ((fun b : Sym2 Γ.Mol => decide ¬b.IsDiag) ∘ (fun e : SEdge Γ.Mol => s(e.src, e.dst)) ∘ SEdge.map Γ.molOf) =
      (fun e : SEdge (E ⊕ I) => decide ¬Γ.InsideMol e.src e.dst) := by
    funext e
    by_cases h : Γ.molOf e.src = Γ.molOf e.dst <;> simp [LGraph.InsideMol, SEdge.map, Sym2.mk_isDiag_iff, h]
  rw [hp]

/-- **(1)** `Γ_{μ,xy}` is a locally standard graph with the external vertices `x = Q.ext 0`, `y = Q.ext 1` (`7_8:794`). -/
def PGraph.LocReg1 (Q : PGraph (Fin 2)) : Prop := Q.LocStd

/-- **(2)** at most `p` internal molecules, and `n_V(𝓜) ≤ n_W(𝓜) + 1` in every molecule (`(eq:MolVW)`, `7_8:796-798`); the vertices counted in
`n_V(𝓜)` are all vertices of the molecule, external ones included. -/
def PGraph.LocReg2 (Q : PGraph (Fin 2)) (p : ℕ) : Prop :=
  Q.g.nM ≤ p ∧ ∀ c : Q.g.Mol, Q.g.molNV c ≤ Q.g.molNW c + 1

/-- **(3)** `W` is a family of `p` walks in the molecular multigraph from `𝓜_x` to `𝓜_y` (`x = Q.ext 0`, `y = Q.ext 1`), pairwise edge-disjoint
(`7_8:801-803`): each walk is the list of its steps `(a, b)`, consecutive steps join, and the multiset of the steps of all walks, read as unordered
pairs of molecules, is contained in the multiset of solid edges between different molecules (`molSolid`), so that no edge is used twice, neither
within a walk nor by two walks.  A walk may revisit a molecule (the paper's paths: delta candidate `T2142a`); if `𝓜_x = 𝓜_y` (the paper assumes
`(eq:far_ab)`, `𝓜_x ≠ 𝓜_y`, `7_8:792`) the walks are closed. -/
def PGraph.LocReg3 (Q : PGraph (Fin 2)) (p : ℕ) (W : Fin p → List (Q.g.Mol × Q.g.Mol)) : Prop :=
  (∀ i, localReg_StepWalk (Q.g.molOf (Sum.inl (Q.ext 0))) (Q.g.molOf (Sum.inl (Q.ext 1))) (W i)) ∧
    (∑ i, localReg_stepEdges (W i)) ≤ Q.g.localReg_molEdgeMS

/-- **(4)** every internal molecule is visited by two different walks of the family `W` (`7_8:805-807`); a walk visits its first molecule and the
second molecule of each of its steps. -/
def PGraph.LocReg4 (Q : PGraph (Fin 2)) (p : ℕ) (W : Fin p → List (Q.g.Mol × Q.g.Mol)) : Prop :=
  ∀ c : Q.g.Mol, ¬ Q.g.IsExtMol c → ∃ i j : Fin p, i ≠ j ∧ localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (W i) c ∧
    localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (W j) c

/-- **(5)** the Hall condition (`7_8:809-813`): for every set `A` of internal molecules, at least `|A|` walks of the family `W` meet `A`. -/
def PGraph.LocReg5 (Q : PGraph (Fin 2)) (p : ℕ) (W : Fin p → List (Q.g.Mol × Q.g.Mol)) : Prop :=
  ∀ A : Finset Q.g.Mol, (∀ c ∈ A, ¬ Q.g.IsExtMol c) →
    A.card ≤ (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (W i) c).card

/-- **(3), (4) and (5)** hold for one common family of walks (`∃ W`): the statement of `lem:localregular` (proved in LW-10b). -/
def PGraph.LocReg345 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := ∃ W, Q.LocReg3 p W ∧ Q.LocReg4 p W ∧ Q.LocReg5 p W

/-- **(6)** the scaling order is at least `2p` (`(eq:sizeGammamu)`, `7_8:815-818`). -/
def PGraph.LocReg6 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := (2 * p : ℤ) ≤ Q.g.scalingOrder

end Predicates

/-- **The counters of the starting graph** (`def scaling`, `(eq:initial_scaling)`, `B:201`): `n_S = 3p`, `n_W = p`, `n_V = 2p`, `n_M = p`. -/
theorem fxyPowGraph_counters (p : ℕ) :
    (fxyPowGraph p).nS = 3 * p ∧ (fxyPowGraph p).nW = p ∧ (fxyPowGraph p).nV = 2 * p ∧ (fxyPowGraph p).nM = p :=
  ⟨(localReg_fxyPowGraph_counters_aux p).1, (localReg_fxyPowGraph_counters_aux p).2.1, (localReg_fxyPowGraph_counters_aux p).2.2, fxyPowGraph_nM p⟩

/-! ## 9. The expansion theorem -/

/-! ## 10. Compiled instances -/

end RBM.Graph
end
