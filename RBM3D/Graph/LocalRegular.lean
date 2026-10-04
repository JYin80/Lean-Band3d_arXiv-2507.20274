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

theorem single (a b : N) : localReg_StepWalk a b [(a, b)] := localReg_StepWalk.cons a b b [] (localReg_StepWalk.nil b)

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

/-- The ends of all steps of a family of walks. -/
def localReg_stepMS {p : ℕ} (W : Fin p → List (N × N)) : Multiset (Sym2 N) := ∑ i, localReg_stepEdges (W i)

/-- The non-diagonal part of a multiset of unordered pairs. -/
def localReg_offDiag (m : Multiset (Sym2 N)) : Multiset (Sym2 N) := m.filter fun s => ¬ s.IsDiag

theorem localReg_offDiag_add (a b : Multiset (Sym2 N)) : localReg_offDiag (a + b) = localReg_offDiag a + localReg_offDiag b := by
  unfold localReg_offDiag; exact Multiset.filter_add _ _ _

theorem localReg_offDiag_le (a : Multiset (Sym2 N)) : localReg_offDiag a ≤ a := Multiset.filter_le _ _

theorem localReg_offDiag_mono {a b : Multiset (Sym2 N)} (h : a ≤ b) : localReg_offDiag a ≤ localReg_offDiag b := by
  unfold localReg_offDiag; exact Multiset.filter_le_filter _ h

theorem localReg_offDiag_of_diag {a : Multiset (Sym2 N)} (h : ∀ s ∈ a, s.IsDiag) : localReg_offDiag a = 0 := by
  unfold localReg_offDiag; exact Multiset.filter_eq_nil.2 fun s hs => not_not.2 (h s hs)

theorem localReg_offDiag_eq_self {a : Multiset (Sym2 N)} (h : ∀ s ∈ a, ¬ s.IsDiag) : localReg_offDiag a = a := by
  unfold localReg_offDiag; exact Multiset.filter_eq_self.2 h

theorem localReg_offDiag_sum {ι : Type*} (s : Finset ι) (f : ι → Multiset (Sym2 N)) :
    localReg_offDiag (∑ i ∈ s, f i) = ∑ i ∈ s, localReg_offDiag (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localReg_offDiag]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, localReg_offDiag_add, ih]

theorem localReg_offDiag_le_of_le_add_diag {a b d : Multiset (Sym2 N)} (hd : ∀ s ∈ d, s.IsDiag) (h : localReg_offDiag a ≤ b + d) :
    localReg_offDiag a ≤ b := by
  classical
  rw [Multiset.le_iff_count] at h ⊢
  intro t
  have h1 := h t
  rw [Multiset.count_add] at h1
  by_cases ht : t.IsDiag
  · have : Multiset.count t (localReg_offDiag a) = 0 := by
      unfold localReg_offDiag; rw [Multiset.count_filter]; simp [ht]
    omega
  · have : Multiset.count t d = 0 := Multiset.count_eq_zero.2 fun hmem => ht (hd t hmem)
    omega

/-- **A family of `p` walks from `u` to `v`** with the budget `B` (the multiset of the available edges): the steps of the
walks that are not loops use distinct edges of `B` (a loop step `(c, c)` is free), and every set `A` of internal nodes
(`Int`) is visited by at least `|A|` of the walks (the Hall condition). -/
def localReg_Fam (p : ℕ) (u v : N) (Int : N → Prop) (B : Multiset (Sym2 N)) : Prop :=
  ∃ W : Fin p → List (N × N), (∀ i, localReg_StepWalk u v (W i)) ∧ localReg_offDiag (localReg_stepMS W) ≤ B ∧
    ∀ A : Finset N, (∀ c ∈ A, Int c) →
      A.card ≤ (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits u (W i) c).card

/-- The family is monotone in the budget. -/
theorem localReg_Fam.mono {p : ℕ} {u v : N} {Int : N → Prop} {B B' : Multiset (Sym2 N)} (h : B ≤ B') :
    localReg_Fam p u v Int B → localReg_Fam p u v Int B' := by
  rintro ⟨W, h1, h2, h3⟩
  exact ⟨W, h1, h2.trans h, h3⟩

/-- Loops cost nothing: a family with the budget `B + D` (`D` loops) has the budget `B`. -/
theorem localReg_Fam.of_add_diag {p : ℕ} {u v : N} {Int : N → Prop} {B D : Multiset (Sym2 N)} (hD : ∀ s ∈ D, s.IsDiag) :
    localReg_Fam p u v Int (B + D) → localReg_Fam p u v Int B := by
  rintro ⟨W, h1, h2, h3⟩
  exact ⟨W, h1, localReg_offDiag_le_of_le_add_diag hD h2, h3⟩


theorem localReg_stepEdges_nil : localReg_stepEdges ([] : List (N × N)) = 0 := rfl

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

/-- The ends of the steps of the mapped walks are the image of the ends of the steps. -/
theorem localReg_stepMS_map {N' : Type*} (ψ : N → N') {p : ℕ} (W : Fin p → List (N × N)) :
    localReg_stepMS (fun i => (W i).map (Prod.map ψ ψ)) = (localReg_stepMS W).map (Sym2.map ψ) := by
  unfold localReg_stepMS
  simp only [localReg_stepEdges_map]
  exact (map_sum (Multiset.mapAddMonoidHom (Sym2.map ψ)) (fun i => localReg_stepEdges (W i)) Finset.univ).symm

/-- **The family is mapped along a map of the nodes** that is onto the internal nodes from internal ones: the walks are mapped, the budget is the image. -/
theorem localReg_Fam.map {N' : Type*} (ψ : N → N') {p : ℕ} {u v : N} {Int : N → Prop} {Int' : N' → Prop}
    {B : Multiset (Sym2 N)} (hI : ∀ c', Int' c' → ∃ c, Int c ∧ ψ c = c') (h : localReg_Fam p u v Int B) :
    localReg_Fam p (ψ u) (ψ v) Int' (B.map (Sym2.map ψ)) := by
  obtain ⟨W, hW, hB, hH⟩ := h
  refine ⟨fun i => (W i).map (Prod.map ψ ψ), fun i => (hW i).map ψ, ?_, ?_⟩
  · rw [localReg_stepMS_map]
    refine le_trans ?_ (Multiset.map_le_map hB)
    unfold localReg_offDiag
    rw [Multiset.filter_map]
    refine Multiset.map_le_map (Multiset.monotone_filter_right _ ?_)
    intro s hs hd
    induction s using Sym2.ind with
    | h a b =>
      apply hs
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hd ⊢
      rw [hd]
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

/-- A replacement walk through a node `X` of a step `(a, b)` or `(b, a)`. -/
theorem localReg_exists_through (X : N) {st : N × N} {a b : N} (hs : s(st.1, st.2) = s(a, b)) :
    ∃ ω : List (N × N), localReg_StepWalk st.1 st.2 ω ∧ localReg_stepEdges ω = {s(a, X), s(X, b)} ∧ ∃ st' ∈ ω, st'.2 = st.2 := by
  rcases Sym2.eq_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨[(a, X), (X, b)], ?_, ?_, ⟨(X, b), by simp, by simp [h2]⟩⟩
    · rw [h1, h2]
      exact localReg_StepWalk.cons a X b _ (localReg_StepWalk.cons X b b [] (localReg_StepWalk.nil b))
    · simp only [localReg_stepEdges, List.map_cons, List.map_nil]; rfl
  · refine ⟨[(b, X), (X, a)], ?_, ?_, ⟨(X, a), by simp, by simp [h2]⟩⟩
    · rw [h1, h2]
      exact localReg_StepWalk.cons b X a _ (localReg_StepWalk.cons X a a [] (localReg_StepWalk.nil a))
    · simp only [localReg_stepEdges, List.map_cons, List.map_nil]
      rw [Sym2.eq_swap (a := b) (b := X), Sym2.eq_swap (a := X) (b := a)]
      change (s(X, b) ::ₘ s(a, X) ::ₘ (0 : Multiset (Sym2 N))) = s(a, X) ::ₘ s(X, b) ::ₘ 0
      exact Multiset.cons_swap _ _ _

/-- **Rerouting through a node.** One use of an edge `{a, b}` of the budget may be replaced by the two edges `{a, X}`, `{X, b}`
(through any node `X`): the walk that used the edge now passes through `X`. -/
theorem localReg_Fam.thr {p : ℕ} {u v : N} {Int : N → Prop} {R : Multiset (Sym2 N)} {a b : N} (X : N)
    (h : localReg_Fam p u v Int (R + {s(a, b)})) : localReg_Fam p u v Int (R + {s(a, X), s(X, b)}) := by
  obtain ⟨W, hW, hB, hH⟩ := h
  by_cases hex : ∃ i, ∃ st ∈ W i, s(st.1, st.2) = s(a, b)
  · obtain ⟨i, st, hst, hs⟩ := hex
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hst
    obtain ⟨ω, hω, hωm, st', hst', hst'e⟩ := localReg_exists_through X hs
    set W' : Fin p → List (N × N) := Function.update W i (A ++ ω ++ B) with hW'
    have hW'i : W' i = A ++ ω ++ B := by simp [hW']
    have hW'j : ∀ j, j ≠ i → W' j = W j := fun j hj => by simp [hW', hj]
    have hAB' := hW i
    rw [hAB] at hAB'
    obtain ⟨x₁, hA, hx₁⟩ := localReg_StepWalk.append_inv hAB'
    obtain ⟨rfl, hB'⟩ := localReg_StepWalk.cons_inv (a := st.1) (b := st.2) (l := B) (by simpa using hx₁)
    have hchain : ∀ j, localReg_StepWalk u v (W' j) := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [hW'i]; exact (hA.append hω).append hB'
      · rw [hW'j j hj]; exact hW j
    refine ⟨W', hchain, ?_, ?_⟩
    · -- the budget
      set rest : Multiset (Sym2 N) := ∑ j ∈ Finset.univ \ {i}, localReg_stepEdges (W j) with hrest
      have h1 : localReg_stepMS W = localReg_stepEdges A + localReg_stepEdges B + rest + {s(a, b)} := by
        unfold localReg_stepMS
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i), hAB, localReg_stepEdges_append, localReg_stepEdges_cons, hs]
        rw [← Multiset.singleton_add]
        abel
      have h2 : localReg_stepMS W' = localReg_stepEdges A + localReg_stepEdges B + rest + {s(a, X), s(X, b)} := by
        unfold localReg_stepMS
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i), hW'i, localReg_stepEdges_append, localReg_stepEdges_append, hωm]
        have : ∑ j ∈ Finset.univ \ {i}, localReg_stepEdges (W' j) = rest := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hW'j j (by simpa using hj)]
        rw [this]
        abel
      have hT : localReg_offDiag (localReg_stepEdges A + localReg_stepEdges B + rest) ≤ R := by
        rw [h1, localReg_offDiag_add] at hB
        by_cases hab : a = b
        · subst hab
          have : localReg_offDiag ({s(a, a)} : Multiset (Sym2 N)) = 0 := localReg_offDiag_of_diag (by simp)
          rw [this, add_zero] at hB
          exact localReg_offDiag_le_of_le_add_diag (d := {s(a, a)}) (by simp) hB
        · have : localReg_offDiag ({s(a, b)} : Multiset (Sym2 N)) = {s(a, b)} := localReg_offDiag_eq_self (by simp [hab])
          rw [this] at hB
          exact Multiset.add_le_add_iff_right.1 hB
      rw [h2, localReg_offDiag_add]
      exact add_le_add hT (localReg_offDiag_le _)
    · intro A' hA'
      refine (hH A' hA').trans (Finset.card_le_card ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      obtain ⟨c, hc, hv⟩ := hj
      refine ⟨c, hc, ?_⟩
      by_cases hji : j = i
      · subst hji
        rw [hW'i]
        rw [hAB] at hv
        rcases hv with hv | ⟨st'', hst'', hst''c⟩
        · exact Or.inl hv
        · right
          simp only [List.mem_append, List.mem_cons] at hst''
          rcases hst'' with hh | hh | hh
          · exact ⟨st'', by simp [hh], hst''c⟩
          · exact ⟨st', by simp [hst'], by rw [hst'e, ← hh, hst''c]⟩
          · exact ⟨st'', by simp [hh], hst''c⟩
      · rw [hW'j j hji]; exact hv
  · push Not at hex
    refine localReg_Fam.mono (Multiset.le_add_right _ _) ⟨W, hW, ?_, hH⟩
    rw [Multiset.le_iff_count]
    intro t
    by_cases ht : t = s(a, b)
    · subst ht
      have h0 : Multiset.count s(a, b) (localReg_stepMS W) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        unfold localReg_stepMS at hmem
        obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hmem
        obtain ⟨st, hst, hst'⟩ := localReg_mem_stepEdges.1 hi
        exact hex i st hst hst'
      have : Multiset.count s(a, b) (localReg_offDiag (localReg_stepMS W)) ≤ Multiset.count s(a, b) (localReg_stepMS W) :=
        Multiset.count_le_of_le _ (localReg_offDiag_le _)
      omega
    · have h1 := Multiset.le_iff_count.1 hB t
      rw [Multiset.count_add, Multiset.count_singleton] at h1
      simp only [ht, ↓reduceIte, add_zero] at h1
      omega

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

/-- **A family of walks with free loops gives a family without loop steps** (using each edge at most once). -/
theorem localReg_Fam.strict {p : ℕ} {u v : N} {Int : N → Prop} {B : Multiset (Sym2 N)} (h : localReg_Fam p u v Int B) :
    ∃ W : Fin p → List (N × N), (∀ i, localReg_StepWalk u v (W i)) ∧ (∀ i, ∀ st ∈ W i, st.1 ≠ st.2) ∧ localReg_stepMS W ≤ B ∧
      ∀ A : Finset N, (∀ c ∈ A, Int c) →
        A.card ≤ (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits u (W i) c).card := by
  obtain ⟨W, hW, hB, hH⟩ := h
  refine ⟨fun i => localReg_stepStrip (W i), fun i => (hW i).strip.1, fun i st hst => ?_, ?_, ?_⟩
  · simpa [localReg_stepStrip] using (List.mem_filter.1 hst).2
  · have : localReg_stepMS (fun i => localReg_stepStrip (W i)) = localReg_offDiag (localReg_stepMS W) := by
      unfold localReg_stepMS
      simp only [localReg_stepEdges_strip]
      rw [localReg_offDiag_sum]
    rw [this]; exact hB
  · intro A hA
    refine (hH A hA).trans (Finset.card_le_card ?_)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨c, hc, hv⟩ := hi
    exact ⟨c, hc, (hW i).strip.2 c hv⟩

/-- **A replacement relation on budgets**: `Rem` may be replaced by `New` in the budget of a family of walks. -/
def localReg_FamRepl (Rem New : Multiset (Sym2 N)) : Prop :=
  ∀ (p : ℕ) (u v : N) (Int : N → Prop) (R : Multiset (Sym2 N)), localReg_Fam p u v Int (R + Rem) → localReg_Fam p u v Int (R + New)

/-- A budget replacement `Rem → New` with `Rem ≤ New`. -/
theorem localReg_FamRepl.of_le {Rem New : Multiset (Sym2 N)} (h : Rem ≤ New) : localReg_FamRepl Rem New :=
  fun _ _ _ _ _ hF => localReg_Fam.mono (add_le_add le_rfl h) hF

/-- A budget replacement of loops by anything. -/
theorem localReg_FamRepl.of_diag {Rem : Multiset (Sym2 N)} (New : Multiset (Sym2 N)) (h : ∀ s ∈ Rem, s.IsDiag) : localReg_FamRepl Rem New :=
  fun _ _ _ _ _ hF => localReg_Fam.mono (Multiset.le_add_right _ _) (localReg_Fam.of_add_diag h hF)

/-- Budget replacements compose. -/
theorem localReg_FamRepl.trans {A B C : Multiset (Sym2 N)} (h₁ : localReg_FamRepl A B) (h₂ : localReg_FamRepl B C) : localReg_FamRepl A C :=
  fun p u v Int R hF => h₂ p u v Int R (h₁ p u v Int R hF)

/-- Budget replacements add. -/
theorem localReg_FamRepl.add {A₁ A₂ B₁ B₂ : Multiset (Sym2 N)} (h₁ : localReg_FamRepl A₁ B₁) (h₂ : localReg_FamRepl A₂ B₂) :
    localReg_FamRepl (A₁ + A₂) (B₁ + B₂) := by
  intro p u v Int R hF
  have e1 : R + (A₁ + A₂) = (R + A₂) + A₁ := by abel
  have h1 := h₁ p u v Int (R + A₂) (by rwa [e1] at hF)
  have e2 : R + A₂ + B₁ = (R + B₁) + A₂ := by abel
  have h2 := h₂ p u v Int (R + B₁) (by rwa [e2] at h1)
  have e3 : R + B₁ + B₂ = R + (B₁ + B₂) := by abel
  rwa [e3] at h2

/-- The replacement of one edge `{a, b}` by `{a, X}, {X, b}`. -/
theorem localReg_FamRepl.thr (a b X : N) : localReg_FamRepl {s(a, b)} {s(a, X), s(X, b)} :=
  fun _ _ _ _ _ hF => localReg_Fam.thr X hF

/-- The identity replacement. -/
theorem localReg_FamRepl.refl (A : Multiset (Sym2 N)) : localReg_FamRepl A A := fun _ _ _ _ _ hF => hF

/-- the replacement of one edge `{a, b}` by `{a, X}, {X, b}`, with loops dropped before and added after -/
theorem localReg_FamRepl.thr' {a b X : N} {D₁ : Multiset (Sym2 N)} (hD : ∀ s ∈ D₁, s.IsDiag) (D₂ : Multiset (Sym2 N)) :
    localReg_FamRepl (D₁ + {s(a, b)}) ({s(a, X), s(X, b)} + D₂) := by
  refine localReg_FamRepl.trans ?_ (localReg_FamRepl.of_le (Multiset.le_add_right _ _))
  have := (localReg_FamRepl.of_diag (0 : Multiset (Sym2 N)) hD).add (localReg_FamRepl.thr a b X)
  simpa using this

/-- the replacement of one edge `{a, b}` by `{a, X}, {X, b}`, the other edges `A` kept -/
theorem localReg_FamRepl.thr3 {a b X : N} {D₁ : Multiset (Sym2 N)} (hD : ∀ s ∈ D₁, s.IsDiag) (A D₂ : Multiset (Sym2 N)) :
    localReg_FamRepl (D₁ + {s(a, b)} + A) ({s(a, X), s(X, b)} + A + D₂) := by
  refine localReg_FamRepl.trans ?_ (localReg_FamRepl.of_le (Multiset.le_add_right _ _))
  have := (localReg_FamRepl.thr' (a := a) (b := b) (X := X) hD 0).add (localReg_FamRepl.refl A)
  simpa using this

/-- the same edges up to loops -/
theorem localReg_FamRepl.same {D₁ : Multiset (Sym2 N)} (hD : ∀ s ∈ D₁, s.IsDiag) (A D₂ : Multiset (Sym2 N)) :
    localReg_FamRepl (D₁ + A) (A + D₂) := by
  refine localReg_FamRepl.trans ?_ (localReg_FamRepl.of_le (Multiset.le_add_right _ _))
  have := (localReg_FamRepl.of_diag (0 : Multiset (Sym2 N)) hD).add (localReg_FamRepl.refl A)
  simpa using this

end Walks

/-! ## 2. The invariant on graphs

`LGraph.localReg_PathFam Γ p x y`: the family of walks on the molecules of `Γ` with the budget of its solid edges.  Transfer along a vertex
map (`localReg_pathFam_map`), along the dotted edge partition (`localReg_pathFam_partition`) and along one expansion term
(`localReg_pathFam_term`). -/

section GraphLevel

/-- The unordered ends of a solid edge. -/
def SEdge.localReg_ends {V : Type*} (e : SEdge V) : Sym2 V := s(e.src, e.dst)

/-- The ends of the image of a solid edge are the image of its ends. -/
theorem SEdge.localReg_ends_map {V W : Type*} (f : V → W) (e : SEdge V) : (SEdge.map f e).localReg_ends = Sym2.map f e.localReg_ends := rfl

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The unordered ends of the solid edges of a graph (weights included), with multiplicity. -/
def LGraph.localReg_endsMS (Γ : LGraph E I) : Multiset (Sym2 (E ⊕ I)) :=
  ((Γ.solid.map SEdge.localReg_ends : List (Sym2 (E ⊕ I))) : Multiset (Sym2 (E ⊕ I)))

/-- The solid edges of a graph as pairs of molecules (the edges inside a molecule give diagonal pairs). -/
def LGraph.localReg_edgeMS (Γ : LGraph E I) : Multiset (Sym2 Γ.Mol) := Γ.localReg_endsMS.map (Sym2.map Γ.molOf)

/-- **The path invariant** at the vertices `x`, `y`: a family of `p` walks from `x`'s molecule to `y`'s molecule in the
molecular multigraph (edge uses at most once, loops free) with the Hall condition on the internal molecules. -/
def LGraph.localReg_PathFam (Γ : LGraph E I) (p : ℕ) (x y : E ⊕ I) : Prop :=
  localReg_Fam p (Γ.molOf x) (Γ.molOf y) (fun c => ¬ Γ.IsExtMol c) Γ.localReg_edgeMS

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

/-- **The invariant along a vertex map** that respects the waved and `=`-dotted edges (up to molecules), sends external
vertices to external vertices and meets every molecule of the target: the walks are mapped. -/
theorem LGraph.localReg_pathFam_map {E₁ I₁ E₂ I₂ : Type} [Fintype E₁] [DecidableEq E₁] [Fintype I₁] [DecidableEq I₁]
    [Fintype E₂] [DecidableEq E₂] [Fintype I₂] [DecidableEq I₂]
    (Γ : LGraph E₁ I₁) (Γ' : LGraph E₂ I₂) (φ : E₁ ⊕ I₁ → E₂ ⊕ I₂)
    (hl : ∀ a : E₁, ∃ a' : E₂, φ (Sum.inl a) = Sum.inl a')
    (hφ : ∀ v', ∃ v, Γ'.molGraph.Reachable v' (φ v))
    (hadj : ∀ u v, Γ.adj u v = true → Γ'.molGraph.Reachable (φ u) (φ v))
    {p : ℕ} {x y : E₁ ⊕ I₁} (h : Γ.localReg_PathFam p x y) :
    localReg_Fam p (Γ'.molOf (φ x)) (Γ'.molOf (φ y)) (fun c => ¬ Γ'.IsExtMol c)
      (Γ.localReg_endsMS.map (Sym2.map fun v => Γ'.molOf (φ v))) := by
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
  have := localReg_Fam.map ψ hI h
  have hb : Γ.localReg_edgeMS.map (Sym2.map ψ) = Γ.localReg_endsMS.map (Sym2.map fun v => Γ'.molOf (φ v)) := by
    unfold LGraph.localReg_edgeMS
    rw [Multiset.map_map]
    congr 1
    funext s
    induction s using Sym2.ind with
    | h a b => simp [hψ]
  rw [hb, hψ, hψ] at this
  exact this

/-- The weight split of a list of solid edges changes the multiset of the ends by loops only (the dropped weights). -/
theorem localReg_lvl1Split_ends {V : Type*} {es es' : List (SEdge V)} {d : ℕ} (h : lvl1Split es es' d) :
    ∃ D : Multiset (Sym2 V), (∀ s ∈ D, s.IsDiag) ∧
      ((es.map SEdge.localReg_ends : List (Sym2 V)) : Multiset (Sym2 V)) =
        ((es'.map SEdge.localReg_ends : List (Sym2 V)) : Multiset (Sym2 V)) + D := by
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
    refine ⟨e.localReg_ends ::ₘ D, ?_, ?_⟩
    · intro s hs
      rcases Multiset.mem_cons.1 hs with rfl | hs
      · simp [SEdge.localReg_ends, h1]
      · exact hD s hs
    · simp only [List.map_cons, ← Multiset.cons_coe, hE]
      rw [Multiset.add_cons]

/-- **The dotted edge partition keeps the invariant** (the merge identifies vertices, the weight split only drops or
circles loops): `Q ∈ Δ.partition m` carries the walks of `Δ`, read through the new external vertices. -/
theorem LGraph.localReg_pathFam_partition (m : ℂ) (Δ : LGraph E I) (Q : PGraph E) (hQ : Q ∈ Δ.partition m) {p : ℕ} {a b : E}
    (h : Δ.localReg_PathFam p (Sum.inl a) (Sum.inl b)) : Q.g.localReg_PathFam p (Sum.inl (Q.ext a)) (Sum.inl (Q.ext b)) := by
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
  have hmap := Δ.localReg_pathFam_map Q.g vm (fun a => ⟨_, hl a⟩) (fun v' => by
    obtain ⟨v, hv⟩ := hsurj v'
    exact ⟨v, by rw [hv]⟩) hadj h
  rw [hl a, hl b] at hmap
  obtain ⟨D, hD, hE⟩ := localReg_lvl1Split_ends hsplit
  have hbud : Δ.localReg_endsMS.map (Sym2.map fun v => Q.g.molOf (vm v)) = Q.g.localReg_edgeMS + D.map (Sym2.map Q.g.molOf) := by
    have e1 : (Δ.localReg_endsMS.map (Sym2.map vm)) = ((Δ.solid.map (SEdge.map vm)).map SEdge.localReg_ends : List _) := by
      unfold LGraph.localReg_endsMS
      rw [Multiset.map_coe, List.map_map, List.map_map]
      rfl
    have e2 : Δ.localReg_endsMS.map (Sym2.map fun v => Q.g.molOf (vm v)) = (Δ.localReg_endsMS.map (Sym2.map vm)).map (Sym2.map Q.g.molOf) := by
      rw [Multiset.map_map]
      congr 1
      funext s
      exact (Sym2.map_map _).symm
    rw [e2, e1, hE, Multiset.map_add]
    rfl
  rw [hbud] at hmap
  refine localReg_Fam.of_add_diag (D := D.map (Sym2.map Q.g.molOf)) ?_ hmap
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
  induction t using Sym2.ind with
  | h x y =>
    have := hD _ ht
    rw [Sym2.mk_isDiag_iff] at this
    simp [Sym2.mk_isDiag_iff, this]

/-- **Stage 1 of a step**: the invariant passes from `Γ` to a term `Δ` that contains the edges of `Γ` on the vertices `emb u`
(`hΓ`, `hΔ`: the ends of the solid edges, read in the molecules of `Δ`), up to a replacement of `Rem` by `New`. -/
theorem LGraph.localReg_pathFam_stage1 {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (Δ : LGraph E I'')
    (emb : E ⊕ I → E ⊕ I'') (hinl : ∀ a, emb (Sum.inl a) = Sum.inl a)
    (hadj : ∀ u v, Γ.adj u v = true → Δ.molGraph.Reachable (emb u) (emb v))
    (hreach : ∀ w, ∃ u, Δ.molGraph.Reachable w (emb u))
    {R Rem New : Multiset (Sym2 Δ.Mol)}
    (hΓ : Γ.localReg_endsMS.map (Sym2.map fun v => Δ.molOf (emb v)) = R + Rem)
    (hΔ : Δ.localReg_edgeMS = R + New) (hrepl : localReg_FamRepl Rem New)
    {p : ℕ} {a b : E} (h : Γ.localReg_PathFam p (Sum.inl a) (Sum.inl b)) : Δ.localReg_PathFam p (Sum.inl a) (Sum.inl b) := by
  have hm := Γ.localReg_pathFam_map Δ emb (fun a => ⟨a, hinl a⟩) hreach hadj h
  rw [hΓ, hinl, hinl] at hm
  have := hrepl p _ _ _ R hm
  rw [← hΔ] at this
  exact this

/-- The twist `(c, t)` of a solid edge keeps its unordered ends. -/
theorem SEdge.localReg_ends_twist {V : Type*} (c t : Bool) (e : SEdge V) : (lwSymmTwistS c t e).localReg_ends = e.localReg_ends := by
  cases c <;> cases t <;> simp [lwSymmTwistS, SEdge.localReg_ends, SEdge.conj, SEdge.transpose, Sym2.eq_swap]

/-- The twist does not change the ends of a list of solid edges. -/
theorem localReg_ends_list_twist {V : Type*} (c t : Bool) (l : List (SEdge V)) :
    (l.map (lwSymmTwistS c t)).map SEdge.localReg_ends = l.map SEdge.localReg_ends := by
  rw [List.map_map]
  exact List.map_congr_left fun e _ => SEdge.localReg_ends_twist c t e

/-- The twist `(c, t)` does not change the molecules. -/
theorem localReg_lwSymmTwistG_molGraph (c t : Bool) (Γ : LGraph E I) : (lwSymmTwistG c t Γ).molGraph = Γ.molGraph := by
  unfold LGraph.molGraph
  rw [lwSymmTwistG_adj]

/-- A permutation of the solid edges does not change the multiset of the ends. -/
theorem LGraph.localReg_endsMS_of_perm {Γ : LGraph E I} {L : List (SEdge (E ⊕ I))} (h : Γ.solid.Perm L) :
    Γ.localReg_endsMS = ((L.map SEdge.localReg_ends : List (Sym2 (E ⊕ I))) : Multiset (Sym2 (E ⊕ I))) :=
  Multiset.coe_eq_coe.2 (h.map _)

/-- The ends of the solid edges of a twisted `owxExt` term: those of the old graph (embedded) and those of the new edges. -/
theorem localReg_endsMS_twistOwx {I'' : Type} [Fintype I''] [DecidableEq I''] (c t : Bool) (G : LGraph E I) (emb : E ⊕ I → E ⊕ I'')
    (cc : ℂ) (N : List (SEdge (E ⊕ I''))) (W : List (WEdge (E ⊕ I''))) :
    (lwSymmTwistG c t (G.owxExt emb cc N W)).localReg_endsMS =
      G.localReg_endsMS.map (Sym2.map emb) + ((N.map SEdge.localReg_ends : List (Sym2 (E ⊕ I''))) : Multiset (Sym2 (E ⊕ I''))) := by
  unfold LGraph.localReg_endsMS
  rw [lvl1_twist_owxExt_solid, List.map_append, ← Multiset.coe_add, localReg_ends_list_twist, Multiset.map_coe]
  congr 2
  rw [List.map_map, List.map_map, List.map_map]
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply]
  rw [SEdge.localReg_ends_map, SEdge.localReg_ends_twist]

/-- `localReg_FamRepl` read through a map `μ` of the vertices to the nodes. -/
def localReg_VRepl {V N' : Type*} (μ : V → N') (A B : Multiset (Sym2 V)) : Prop :=
  localReg_FamRepl (A.map (Sym2.map μ)) (B.map (Sym2.map μ))

/-- **A term of the three expansions, as a packed graph step**: `Δ = (G.owxExt emb cc N W)` twisted by `(c, t)`, where `G`
has the molecules of `Γ` and `Γ`'s solid edges are `Rm` and `G`'s: the invariant passes from `Γ` to `Δ` up to the replacement of
the (images of) `Rm` by the new edges `N`, whatever the map `μ` of the vertices to the nodes is, provided it is constant on the
molecules of the untwisted `G.owxExt emb cc N W`. -/
theorem localReg_pathFam_term {I'' : Type} [Fintype I''] [DecidableEq I''] (Γ G : LGraph E I) (c t : Bool) (emb : E ⊕ I → E ⊕ I'')
    (cc : ℂ) (N : List (SEdge (E ⊕ I''))) (W : List (WEdge (E ⊕ I'')))
    (hG : G.adj = Γ.adj) (hinl : ∀ a, emb (Sum.inl a) = Sum.inl a)
    (hreach : ∀ w, ∃ u, (G.owxExt emb cc N W).molGraph.Reachable w (emb u))
    (Rm : Multiset (Sym2 (E ⊕ I))) (hΓ : Γ.localReg_endsMS = Rm + G.localReg_endsMS)
    (hrepl : ∀ (N' : Type) (μ : E ⊕ I'' → N'),
      (∀ u v, (G.owxExt emb cc N W).molGraph.Reachable u v → μ u = μ v) →
        localReg_VRepl μ (Rm.map (Sym2.map emb)) ((N.map SEdge.localReg_ends : List (Sym2 (E ⊕ I''))) : Multiset (Sym2 (E ⊕ I''))))
    {p : ℕ} {a b : E} (h : Γ.localReg_PathFam p (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (G.owxExt emb cc N W)).localReg_PathFam p (Sum.inl a) (Sum.inl b) := by
  set Δ := lwSymmTwistG c t (G.owxExt emb cc N W) with hΔ
  have hmol : Δ.molGraph = (G.owxExt emb cc N W).molGraph := localReg_lwSymmTwistG_molGraph c t _
  have hμ : ∀ u v, (G.owxExt emb cc N W).molGraph.Reachable u v → Δ.molOf u = Δ.molOf v :=
    fun u v huv => SimpleGraph.ConnectedComponent.eq.2 (by rw [hmol]; exact huv)
  have e1 : (Rm.map (Sym2.map emb)).map (Sym2.map Δ.molOf) = Rm.map (Sym2.map fun v => Δ.molOf (emb v)) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun s _ => Sym2.map_map s
  refine LGraph.localReg_pathFam_stage1 Γ Δ emb hinl ?_ (fun w => ?_) (R := G.localReg_endsMS.map (Sym2.map fun v => Δ.molOf (emb v)))
    (Rem := Rm.map (Sym2.map fun v => Δ.molOf (emb v)))
    (New := ((N.map SEdge.localReg_ends : List (Sym2 (E ⊕ I''))) : Multiset (Sym2 (E ⊕ I''))).map (Sym2.map Δ.molOf)) ?_ ?_ ?_ h
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
  · rw [hΓ, Multiset.map_add, add_comm]
  · have e0 : Δ.localReg_endsMS = G.localReg_endsMS.map (Sym2.map emb) +
        ((N.map SEdge.localReg_ends : List (Sym2 (E ⊕ I''))) : Multiset (Sym2 (E ⊕ I''))) :=
      localReg_endsMS_twistOwx c t G emb cc N W
    have e1' : (G.localReg_endsMS.map (Sym2.map emb)).map (Sym2.map Δ.molOf) =
        G.localReg_endsMS.map (Sym2.map fun v => Δ.molOf (emb v)) := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun s _ => Sym2.map_map s
    unfold LGraph.localReg_edgeMS
    rw [e0, Multiset.map_add, e1']
  · have := hrepl Δ.Mol Δ.molOf hμ
    unfold localReg_VRepl at this
    rwa [e1] at this

/-- The two edges of the derivative `owxDE a w e` of an edge `e`, read in molecules with `μ a = μ w`, are `{μ e.src, μ w}`, `{μ w, μ e.dst}`. -/
theorem localReg_owxDE_ends_mol {V N' : Type*} (μ : V → N') (a w : V) (hμ : μ a = μ w) (e : SEdge V) :
    ({Sym2.map μ (owxDE a w e).1.localReg_ends, Sym2.map μ (owxDE a w e).2.localReg_ends} : Multiset (Sym2 N')) =
      {s(μ e.src, μ w), s(μ w, μ e.dst)} := by
  unfold owxDE
  split_ifs
  · simp [SEdge.localReg_ends, hμ]
  · simp [SEdge.localReg_ends, hμ]

/-- **The derivative replacement** (`owxDE`): an edge `e` is replaced by the two edges of its derivative at `(a, w)`, where `a` and `w` lie
in one molecule: the walk through `e` goes through that molecule.  The other edges `A` stay (as `A'`, equal in the molecules). -/
theorem localReg_VRepl.deriv {V N' : Type*} (μ : V → N') (a w : V) (hμ : μ a = μ w) (e : SEdge V) {Rm New : Multiset (Sym2 V)}
    (D₁ A A' D₂ : Multiset (Sym2 V)) (hD₁ : ∀ s ∈ D₁, (Sym2.map μ s).IsDiag)
    (hAA : A.map (Sym2.map μ) = A'.map (Sym2.map μ))
    (hRm : Rm = D₁ + {e.localReg_ends} + A) (hNew : New = {(owxDE a w e).1.localReg_ends, (owxDE a w e).2.localReg_ends} + A' + D₂) :
    localReg_VRepl μ Rm New := by
  subst hRm hNew
  unfold localReg_VRepl
  have h := localReg_owxDE_ends_mol μ a w hμ e
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.insert_eq_cons, Multiset.map_cons] at h ⊢
  rw [h, ← hAA]
  exact localReg_FamRepl.thr3 (a := μ e.src) (b := μ e.dst) (X := μ w) (D₁ := D₁.map (Sym2.map μ))
    (by intro s hs; obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs; exact hD₁ t ht) _ _

/-- **The same edges up to loops and molecules**: `Rm = D₁ + A` (`D₁` loops in the molecules), `New = A' + D₂` with `A'` the edges
`A` read in the molecules. -/
theorem localReg_VRepl.same {V N' : Type*} (μ : V → N') {Rm New : Multiset (Sym2 V)} (D₁ A A' D₂ : Multiset (Sym2 V))
    (hD₁ : ∀ s ∈ D₁, (Sym2.map μ s).IsDiag) (hAA : A.map (Sym2.map μ) = A'.map (Sym2.map μ))
    (hRm : Rm = D₁ + A) (hNew : New = A' + D₂) : localReg_VRepl μ Rm New := by
  subst hRm hNew
  unfold localReg_VRepl
  simp only [Multiset.map_add]
  rw [← hAA]
  exact localReg_FamRepl.same (D₁ := D₁.map (Sym2.map μ))
    (by intro s hs; obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs; exact hD₁ t ht) _ _

/-- The unordered ends of a solid edge given by its fields. -/
@[simp] theorem SEdge.localReg_ends_mk {V : Type*} (σ c : Bool) (a b : V) : (⟨σ, c, a, b⟩ : SEdge V).localReg_ends = s(a, b) := rfl

local macro "localReg_msnorm" : tactic => `(tactic| (simp only [SEdge.localReg_ends_mk, SEdge.localReg_ends_map, Sym2.map_mk, lwSymmTwistP, List.map_cons, List.map_nil,
  Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe, Multiset.coe_nil,
  Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq]; try abel))

/-- The image of an internal vertex under the embedding `owxEmb`. -/
theorem localReg_owxEmb_inr_eq {E I : Type*} (k : ℕ) (x : I) : owxEmb k (Sum.inr x : E ⊕ I) = Sum.inr (Sum.inl x) := rfl

local macro "localReg_msnormx" : tactic => `(tactic| (simp only [SEdge.localReg_ends_mk, SEdge.localReg_ends_map, Sym2.map_mk, lwSymmTwistP, List.map_cons, List.map_nil,
  Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, ← Multiset.cons_coe, Multiset.coe_nil,
  Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add, id_eq, localReg_owxEmb_inr_eq]; try abel))

/-! ## 3. The terms of the three expansions

One lemma for each output term of `(Owx)`, `(Oe1x)`, `(Oe2x)` (the twisted `owxExt` terms of `Graph/LWSymm.lean`): the edges removed and the
edges added, read in the molecules (the new vertices lie in the molecule of `x`), and the replacement of the former by the latter
(`localReg_VRepl`). -/

section Terms

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `(Owx)` term 3 for the solid edge `q.1 = (a, b)` of `f`: the weight `p.1` is dropped and `q.1` is replaced by the two edges of its derivative, a walk `M(a) → M(x) → M(b)` (`B:184-196`, the second alternative). -/
theorem localReg_pathFam_owxT3 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) : (lwSymmOwxT3 c t m Γ x q).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT3 owxET3
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 1 x w, lwSymmExt_reach1 _ x _ _ _ false true (by simp) w⟩
  · have h1 := lwSplit_perm Γ.solid p hp
    have h2 := lwSplit_perm p.2 q hq
    have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := h1.trans (h2.cons p.1)
    rw [LGraph.localReg_endsMS_of_perm h3]
    unfold LGraph.localReg_endsMS
    show _ = _ + (((q.2.map (lwSymmTwistS c t)).map SEdge.localReg_ends : List (Sym2 (E ⊕ I))) : Multiset (Sym2 (E ⊕ I)))
    rw [localReg_ends_list_twist]
    simp only [List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist, Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 x) :=
      hμ _ _ (lwSymmExt_reach1 _ x _ _ _ false true (by simp) (Sum.inr (Sum.inr 0)))
    refine localReg_VRepl.deriv μ (Sum.inr (Sum.inr 0)) (owxEmb 1 x) hα (SEdge.map (owxEmb 1) (lwSymmTwistS c t q.1))
      {s(owxEmb 1 x, owxEmb 1 x)} 0 0 {s(Sum.inr (Sum.inr 0), owxEmb 1 x)} (by simp) rfl ?_ ?_
    · rw [hx] <;> localReg_msnorm
    · localReg_msnorm

/-- `(Owx)` term 1 (`m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f`): the frame is kept, the leaf `α` joins the molecule of `x`; no solid edge of `Γ` is removed. -/
theorem localReg_pathFam_owxT1 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (c t : Bool) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) : (lwSymmOwxT1 c t m Γ x).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT1 owxET1
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ 0 ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 1 x w, lwSymmExt_reach1 _ x _ _ _ false true (by simp) w⟩
  · rw [zero_add]
    unfold LGraph.localReg_endsMS
    rw [lwSymmTwistG_solid, localReg_ends_list_twist]
  · intro N' μ hμ
    unfold localReg_VRepl
    simp only [Multiset.map_zero]
    exact localReg_FamRepl.of_le (Multiset.zero_le _)

/-- `(Owx)` term 2: the weight `p.1` (a loop inside the molecule of `x`) is dropped, the path `x - α - β` is added; a loop costs nothing. -/
theorem localReg_pathFam_owxT2 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) : (lwSymmOwxT2 c t m Γ p x).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT2 owxET2
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ ((lwSymmTwistS c t p.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 2 x w, lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) w⟩
  · have h1 := lwSplit_perm Γ.solid p hp
    rw [LGraph.localReg_endsMS_of_perm h1]
    unfold LGraph.localReg_endsMS
    show _ = _ + (((p.2.map (lwSymmTwistS c t)).map SEdge.localReg_ends : List (Sym2 (E ⊕ I))) : Multiset (Sym2 (E ⊕ I)))
    rw [localReg_ends_list_twist]
    simp only [List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist, Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    unfold localReg_VRepl
    refine localReg_FamRepl.of_diag _ ?_
    intro s hs
    rw [hx] at hs
    simp only [Multiset.map_cons, Multiset.map_zero, SEdge.localReg_ends_mk, Sym2.map_mk, Multiset.mem_cons] at hs
    rcases hs with rfl | hs
    · simp [Sym2.mk_isDiag_iff]
    · exact absurd hs (Multiset.notMem_zero _)

/-- `(Owx)` term 4 for `q.1 = (a, b)`: as term 3, with the new path `x - α - β` and the derivative at `(β, α)`. -/
theorem localReg_pathFam_owxT4 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) : (lwSymmOwxT4 c t m Γ x q).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOwxT4 owxET4
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact lwSymmTwistG_adj c t Γ
  · exact fun w => ⟨lwSymmRho 2 x w, lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) w⟩
  · have h1 := lwSplit_perm Γ.solid p hp
    have h2 := lwSplit_perm p.2 q hq
    have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := h1.trans (h2.cons p.1)
    rw [LGraph.localReg_endsMS_of_perm h3]
    unfold LGraph.localReg_endsMS
    show _ = _ + (((q.2.map (lwSymmTwistS c t)).map SEdge.localReg_ends : List (Sym2 (E ⊕ I))) : Multiset (Sym2 (E ⊕ I)))
    rw [localReg_ends_list_twist]
    simp only [List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist, Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 2 x) :=
      hμ _ _ (lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (owxEmb 2 x) :=
      hμ _ _ (lwSymmExt_reach2 _ x _ _ _ true true false true (by simp) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg_VRepl.deriv μ (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (hβ.trans hα.symm)
      (SEdge.map (owxEmb 2) (lwSymmTwistS c t q.1)) {s(owxEmb 2 x, owxEmb 2 x)} 0 0
      {(⟨true, false, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0)⟩ : SEdge _).localReg_ends} (by simp) rfl ?_ ?_
    · rw [hx] <;> localReg_msnorm
    · localReg_msnorm

/-- The frame of a selected edge has the molecules (the adjacency) of the graph. -/
theorem localReg_lwSymmFrame_adj (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).adj = Γ.adj := lwSymmTwistG_adj c t (lwSymmUncirc Γ p)

/-- The frame of two selected edges has the molecules (the adjacency) of the graph. -/
theorem localReg_lwSymmFrame2_adj (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).adj = Γ.adj := lwSymmTwistG_adj c t (lwSymmUncirc2 Γ p q)

/-- The frame has the multiset of the ends of the solid edges of the graph (the twist and the uncircling keep the ends). -/
theorem localReg_lwSymmFrame_endsMS (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) : (lwSymmFrame c t Γ p).localReg_endsMS = Γ.localReg_endsMS := by
  rw [LGraph.localReg_endsMS_of_perm (lwSplit_perm Γ.solid p hp)]
  unfold LGraph.localReg_endsMS
  rw [lwSymmFrame_solid]
  simp only [lwSymmFrameP, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist, localReg_ends_list_twist]
  rfl

/-- The frame of two selected edges has the multiset of the ends of the solid edges of the graph. -/
theorem localReg_lwSymmFrame2_endsMS (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) : (lwSymmFrame2 c t Γ p q).localReg_endsMS = Γ.localReg_endsMS := by
  have h3 : Γ.solid.Perm (p.1 :: q.1 :: q.2) := (lwSplit_perm Γ.solid p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)
  rw [LGraph.localReg_endsMS_of_perm h3]
  unfold LGraph.localReg_endsMS
  rw [lwSymmFrame2_solid]
  simp only [lwSymmFrame2P, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist, localReg_ends_list_twist]
  rfl

/-- `(Oe1x)`, the term `m Σ_α S_{xα} Ǧ_{αα} 𝒢`: the frame is kept, a leaf `α` joins the molecule of `x`. -/
theorem localReg_pathFam_oe1xOwx (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (c t : Bool) {k : ℕ} {a b : E} (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe1xOwx c t m Γ p x).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe1xOwx owxT1
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ 0 ?_ ?_ h
  · exact localReg_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [zero_add, localReg_lwSymmFrame_endsMS c t Γ p hp]
  · intro N' μ hμ
    unfold localReg_VRepl
    simp only [Multiset.map_zero]
    exact localReg_FamRepl.of_le (Multiset.zero_le _)

/-- the perm of the solid edges for the two selected edges -/
theorem localReg_lwSplit_perm2 (l : List (SEdge (E ⊕ I))) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit l)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) : l.Perm (p.1 :: q.1 :: q.2) :=
  (lwSplit_perm l p hp).trans ((lwSplit_perm p.2 q hq).cons p.1)

/-- `(Oe1x)`, the derivative term for the edge `q.1 = (a, b)` of the rest: `e_0 = (x, v)` becomes `(α, v)` (the same molecular edge, `α ∈ M(x)`), `q.1` is replaced through the molecule of `x`. -/
theorem localReg_pathFam_oe1xD (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xD m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xD
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    refine localReg_VRepl.deriv μ (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) hα
      (SEdge.map (owxEmb 1) (lwSymmTwistS c t q.1)) 0 {s(owxEmb 1 (Sum.inr x), owxEmb 1 v)}
      {s(Sum.inr (Sum.inr 0), owxEmb 1 v)} 0 (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_singleton, Sym2.map_mk, hα]
    · rw [hx] <;> localReg_msnorm
    · localReg_msnorm

/-- `(Oe1x)`, the term with the loop `Ǧ̄_{xx}` circled, for a red out-edge `q.1 = (x, d)` of `x`: `e_0` and `q.1` move from `x` to `α ∈ M(x)`, the molecular edges are unchanged. -/
theorem localReg_pathFam_oe1xP5 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hs : (lwSymmTwistS c t q.1).src = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP5 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP5
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg_ends = s(Sum.inr x, (lwSymmTwistS c t q.1).dst) := by simp [SEdge.localReg_ends, hs]
    refine localReg_VRepl.same μ 0 {s(owxEmb 1 (Sum.inr x), owxEmb 1 v), s(owxEmb 1 (Sum.inr x), owxEmb 1 (lwSymmTwistS c t q.1).dst)}
      {s(Sum.inr (Sum.inr 0), owxEmb 1 (lwSymmTwistS c t q.1).dst), s(Sum.inr (Sum.inr 0), owxEmb 1 v)}
      {s(Sum.inr (Sum.inl x), Sum.inr (Sum.inl x))} (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hx, hqe]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe1x)`, the term with the loop `Ḡ_{xx}` replaced by the constant `m̄`, for a red out-edge of `x`: the molecular edges are unchanged. -/
theorem localReg_pathFam_oe1xP3 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hs : (lwSymmTwistS c t q.1).src = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP3 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP3
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg_ends = s(Sum.inr x, (lwSymmTwistS c t q.1).dst) := by simp [SEdge.localReg_ends, hs]
    refine localReg_VRepl.same μ 0 {s(owxEmb 1 (Sum.inr x), owxEmb 1 v), s(owxEmb 1 (Sum.inr x), owxEmb 1 (lwSymmTwistS c t q.1).dst)}
      {s(Sum.inr (Sum.inr 0), owxEmb 1 (lwSymmTwistS c t q.1).dst), s(Sum.inr (Sum.inr 0), owxEmb 1 v)}
      0 (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hx, hqe]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe1x)`, the term with the loop `Ǧ_{xx}` circled, for a blue in-edge `q.1 = (s, x)` of `x`: the molecular edges are unchanged. -/
theorem localReg_pathFam_oe1xP6 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hd : (lwSymmTwistS c t q.1).dst = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP6 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP6
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg_ends = s((lwSymmTwistS c t q.1).src, Sum.inr x) := by simp [SEdge.localReg_ends, hd]
    refine localReg_VRepl.same μ 0 {s(owxEmb 1 (Sum.inr x), owxEmb 1 v), s(owxEmb 1 (lwSymmTwistS c t q.1).src, owxEmb 1 (Sum.inr x))}
      {s(owxEmb 1 (lwSymmTwistS c t q.1).src, Sum.inr (Sum.inr 0)), s(Sum.inr (Sum.inr 0), owxEmb 1 v)}
      {s(Sum.inr (Sum.inl x), Sum.inr (Sum.inl x))} (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hx, hqe]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe1x)`, the term with the loop `G_{xx}` replaced by the constant `m`, for a blue in-edge of `x`: the molecular edges are unchanged. -/
theorem localReg_pathFam_oe1xP4 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hd : (lwSymmTwistS c t q.1).dst = Sum.inr x) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmTwistG c t (oe1xP4 m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q))).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold oe1xP4
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame_adj c t Γ p
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    have hqe : (lwSymmTwistS c t q.1).localReg_ends = s((lwSymmTwistS c t q.1).src, Sum.inr x) := by simp [SEdge.localReg_ends, hd]
    refine localReg_VRepl.same μ 0 {s(owxEmb 1 (Sum.inr x), owxEmb 1 v), s(owxEmb 1 (lwSymmTwistS c t q.1).src, owxEmb 1 (Sum.inr x))}
      {s(owxEmb 1 (lwSymmTwistS c t q.1).src, Sum.inr (Sum.inr 0)), s(Sum.inr (Sum.inr 0), owxEmb 1 v)}
      0 (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hx, hqe]; localReg_msnorm
    · localReg_msnorm

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

/-- `(Oe2x)`, `R2` (`m³ S⁺_{xy} G_{y'y} f`): the waved edge `x ~ y` merges the molecules of `x` and `y`, `p.1 = (x, y)` becomes a loop, `q.1 = (y', x)` becomes `(y', y)`. -/
theorem localReg_pathFam_oe2xR2 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR2 c t m Γ p q x y y').localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR2 oe2xR2
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨w, SimpleGraph.Reachable.refl _⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmFrame2Q, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hxy : μ (Sum.inr x) = μ y :=
      hμ _ _ (LGraph.localReg_reach_of_waved _ ⟨true, true, Sum.inr x, y⟩ (by simp [LGraph.owxExt]))
    refine localReg_VRepl.same μ {s(Sum.inr x, y)} {s(y', Sum.inr x)} {s(y', y)} 0 (by simp [Sym2.mk_isDiag_iff, hxy]) ?_ ?_ ?_
    · simp only [Multiset.map_singleton, Sym2.map_mk, hxy]
    · rw [hp1, hq1]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe2x)`, `R3 = (Owx)` term 1 on the frame: a leaf `α` joins the molecule of `x`. -/
theorem localReg_pathFam_oe2xR3 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (c t : Bool) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR3 c t m Γ p q x).localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR3 owxT1
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_ 0 ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [zero_add, localReg_lwSymmFrame2_endsMS c t Γ p q hp hq]
  · intro N' μ hμ
    unfold localReg_VRepl
    simp only [Multiset.map_zero]
    exact localReg_FamRepl.of_le (Multiset.zero_le _)

/-- `(Oe2x)`, `R4`: the edges `(x, y)`, `(y', x)` move to `(α, y)`, `(y', α)` with `α ∈ M(x)` (the molecular edges are unchanged). -/
theorem localReg_pathFam_oe2xR4 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR4 c t m Γ p q x y y').localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR4 oe2xR4
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 2 (Sum.inr x) w, lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmFrame2Q, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 2 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 0)))
    refine localReg_VRepl.same μ 0 {s(owxEmb 2 (Sum.inr x), owxEmb 2 y), s(owxEmb 2 y', owxEmb 2 (Sum.inr x))}
      {s(Sum.inr (Sum.inr 0), owxEmb 2 y), s(owxEmb 2 y', Sum.inr (Sum.inr 0))}
      {s(Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1))} (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hp1, hq1]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe2x)`, `R5`: the edges `(x, y)`, `(y', x)` move to `(α, y)`, `(y', α)` with `α ∈ M(x)`. -/
theorem localReg_pathFam_oe2xR5 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR5 c t m Γ p q x y y').localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR5 oe2xR5
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmFrame2Q, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (owxEmb 1 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    refine localReg_VRepl.same μ 0 {s(owxEmb 1 (Sum.inr x), owxEmb 1 y), s(owxEmb 1 y', owxEmb 1 (Sum.inr x))}
      {s(Sum.inr (Sum.inr 0), owxEmb 1 y), s(owxEmb 1 y', Sum.inr (Sum.inr 0))}
      {s(Sum.inr (Sum.inl x), Sum.inr (Sum.inl x))} (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hp1, hq1]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe2x)`, `R6`: the edges `(x, y)`, `(y', x)` move to `(β, y)`, `(y', β)` with `β ∈ M(x)`. -/
theorem localReg_pathFam_oe2xR6 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR6 c t m Γ p q x y y').localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR6 oe2xR6
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 2 (Sum.inr x) w, lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm2 _ p hp q hq)]
    simp only [LGraph.localReg_endsMS, lwSymmFrame2Q, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (owxEmb 2 (Sum.inr x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg_VRepl.same μ 0 {s(owxEmb 2 (Sum.inr x), owxEmb 2 y), s(owxEmb 2 y', owxEmb 2 (Sum.inr x))}
      {s(Sum.inr (Sum.inr 1), owxEmb 2 y), s(owxEmb 2 y', Sum.inr (Sum.inr 1))}
      {s(Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0))} (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hβ, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hp1, hq1]; localReg_msnorm
    · localReg_msnorm

/-- `(Oe2x)`, `R7` for the edge `q'.1` of `f`: `(x, y)` becomes `(α, y)`, `(y', x)` stays, `q'.1` is replaced by the two edges of its derivative through `M(x)`. -/
theorem localReg_pathFam_oe2xR7 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR7 c t m Γ p q x y y' q').localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR7 oe2xR7
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ (lwSymmTwistS c t q'.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 1 (Sum.inr x) w, lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm3 _ p hp q hq q' hq')]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (Sum.inr (Sum.inl x)) :=
      hμ _ _ (lwSymmExt_reach1 _ (Sum.inr x) _ _ _ false true (by simp [owxEmb]) (Sum.inr (Sum.inr 0)))
    refine localReg_VRepl.deriv μ (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) hα
      (SEdge.map (owxEmb 1) (lwSymmTwistS c t q'.1)) 0
      {s(Sum.inr (Sum.inl x), owxEmb 1 y), s(owxEmb 1 y', Sum.inr (Sum.inl x))}
      {s(owxEmb 1 y', Sum.inr (Sum.inl x)), s(Sum.inr (Sum.inr 0), owxEmb 1 y)} 0 (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hp1, hq1]; localReg_msnormx
    · localReg_msnormx

/-- `(Oe2x)`, `R8` for the edge `q'.1` of `f`: `(x, y)`, `(y', x)` move to `(β, y)`, `(y', α)`, `q'.1` is replaced by its derivative at `(β, α)` through `M(x)`. -/
theorem localReg_pathFam_oe2xR8 (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq' : q' ∈ lwSplit q.2) {k : ℕ} {a b : E}
    (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    (lwSymmOe2xR8 c t m Γ p q x y y' q').localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe2xR8 oe2xR8
  refine localReg_pathFam_term Γ _ c t _ _ _ _ ?_ (fun a => rfl) ?_
    ((lwSymmTwistS c t p.1).localReg_ends ::ₘ (lwSymmTwistS c t q.1).localReg_ends ::ₘ (lwSymmTwistS c t q'.1).localReg_ends ::ₘ 0) ?_ ?_ h
  · exact localReg_lwSymmFrame2_adj c t Γ p q
  · exact fun w => ⟨lwSymmRho 2 (Sum.inr x) w, lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) w⟩
  · rw [LGraph.localReg_endsMS_of_perm (localReg_lwSplit_perm3 _ p hp q hq q' hq')]
    simp only [LGraph.localReg_endsMS, lwSymmTwistP, localReg_ends_list_twist, List.map_cons, ← Multiset.cons_coe, SEdge.localReg_ends_twist,
      Multiset.cons_add, Multiset.zero_add]
  · intro N' μ hμ
    have hα : μ (Sum.inr (Sum.inr 0)) = μ (Sum.inr (Sum.inl x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 0)))
    have hβ : μ (Sum.inr (Sum.inr 1)) = μ (Sum.inr (Sum.inl x)) :=
      hμ _ _ (lwSymmExt_reach2 _ (Sum.inr x) _ _ _ true true false true (by simp [owxEmb]) (by simp) (Sum.inr (Sum.inr 1)))
    refine localReg_VRepl.deriv μ (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (hβ.trans hα.symm)
      (SEdge.map (owxEmb 2) (lwSymmTwistS c t q'.1)) 0
      {s(Sum.inr (Sum.inl x), owxEmb 2 y), s(owxEmb 2 y', Sum.inr (Sum.inl x))}
      {s(Sum.inr (Sum.inr 1), owxEmb 2 y), s(owxEmb 2 y', Sum.inr (Sum.inr 0))} 0 (by simp) ?_ ?_ ?_
    · simp only [Multiset.map_cons, Multiset.map_zero, Multiset.map_singleton, Multiset.map_add, Multiset.insert_eq_cons,
        Sym2.map_mk, hα, hβ, ← Multiset.singleton_add, add_zero, zero_add]
      try abel
    · rw [hp1, hq1]; localReg_msnormx
    · localReg_msnormx

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

/-- `fxyPowGraph 2` is the merged `p2Graph` (`(eq:p=2graph)`): equal, with the same vertex order (not only up to a relabelling). -/
theorem fxyPowGraph_two : fxyPowGraph 2 = p2Graph := by
  rfl


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

/-- **The walks of the starting graph**: `x → α_i → y` through the molecule `{α_i, β_i}`. -/
theorem localReg_fxyPowGraph_pathFam (p : ℕ) : (fxyPowGraph p).localReg_PathFam p (Sum.inl 0) (Sum.inl 1) := by
  classical
  set Mx := (fxyPowGraph p).molOf (Sum.inl 0) with hMx
  set My := (fxyPowGraph p).molOf (Sum.inl 1) with hMy
  refine ⟨fun i => [(Mx, localReg_fxyMol i), (localReg_fxyMol i, My)], fun i => ?_, ?_, ?_⟩
  · exact localReg_StepWalk.cons _ _ _ _ (localReg_StepWalk.cons _ _ _ _ (localReg_StepWalk.nil _))
  · refine (localReg_offDiag_le _).trans ?_
    have hs : (fxyPowGraph p).solid = (List.finRange p).flatMap (localReg_fxyBlock p) := rfl
    unfold localReg_stepMS LGraph.localReg_edgeMS LGraph.localReg_endsMS
    rw [Multiset.map_coe, List.map_map, hs, List.map_flatMap, localReg_coe_flatMap_eq_sum, ← Fin.sum_univ_def]
    refine Finset.sum_le_sum fun i _ => ?_
    unfold localReg_stepEdges
    rw [Multiset.coe_le]
    exact List.Sublist.subperm (.cons _ (.cons_cons _ (.cons_cons _ .slnil)))
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

section Assembly

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The invariant for every term of `lwSymmOe1xDs` (the derivative terms of `(Oe1x)`: the cases `oe1xD`, `oe1xP5/P3`, `oe1xP6/P4` of `oe1xDs`). -/
theorem localReg_pathFam_oe1xDs (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (x : I) (v : E ⊕ I) (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (T : LGraph E (I ⊕ Fin 1))
    (hT : T ∈ lwSymmOe1xDs c t m Γ p x v q) {k : ℕ} {a b : E} (h : Γ.localReg_PathFam k (Sum.inl a) (Sum.inl b)) :
    T.localReg_PathFam k (Sum.inl a) (Sum.inl b) := by
  unfold lwSymmOe1xDs at hT
  obtain ⟨T0, hT0, rfl⟩ := List.mem_map.1 hT
  unfold oe1xDs at hT0
  by_cases h1 : (lwSymmTwistP c t q).1.σ = false ∧ (lwSymmTwistP c t q).1.src = Sum.inr x
  · simp only [h1, and_self, ↓reduceIte] at hT0
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT0
    rcases hT0 with rfl | rfl
    · exact localReg_pathFam_oe1xP5 m Γ p hp x v c t hx q hq h1.2 h
    · exact localReg_pathFam_oe1xP3 m Γ p hp x v c t hx q hq h1.2 h
  · simp only [h1, ↓reduceIte] at hT0
    by_cases h2 : (lwSymmTwistP c t q).1.σ = true ∧ (lwSymmTwistP c t q).1.dst = Sum.inr x
    · simp only [h2, and_self, ↓reduceIte] at hT0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT0
      rcases hT0 with rfl | rfl
      · exact localReg_pathFam_oe1xP6 m Γ p hp x v c t hx q hq h2.2 h
      · exact localReg_pathFam_oe1xP4 m Γ p hp x v c t hx q hq h2.2 h
    · simp only [h2, ↓reduceIte] at hT0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT0
      rw [hT0]
      exact localReg_pathFam_oe1xD m Γ p hp x v c t hx q hq h

/-- **The path invariant of a packed graph with two external vertices** `x = Q.ext 0`, `y = Q.ext 1`: `p` edge-disjoint walks in the molecular
multigraph from the molecule of `x` to that of `y`, with the Hall condition on the internal molecules (loop steps are free). -/
def PGraph.PathInv (p : ℕ) (Q : PGraph (Fin 2)) : Prop :=
  Q.g.localReg_PathFam p (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1))

/-- **The invariant passes along every `LocStep`** (the three cases `B:178-199`, for the outputs of `(Owx)`, `(Oe1x)`, `(Oe2x)` after the dotted
edge partition). -/
theorem pathInv_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs) {k : ℕ}
    (hP : P.PathInv k) : ∀ B ∈ outs, B.PathInv k := by
  have key : ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I''),
      T.localReg_PathFam k (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) →
        ∀ Q0 ∈ T.partition m, (Q0.lvl1Comp P.ext P.ext_surj).PathInv k :=
    fun T hT Q0 hQ0 => LGraph.localReg_pathFam_partition m T Q0 hQ0 hT
  intro B hB
  cases hst with
  | weight p hp x c t hx =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1WeightOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with ((hQ | hQ) | ⟨q, hq, hQ⟩) | ⟨q, hq, hQ⟩
    · exact key _ (localReg_pathFam_owxT1 m P.g x c t hP) Q0 hQ
    · exact key _ (localReg_pathFam_owxT2 m P.g p hp x c t hx hP) Q0 hQ
    · exact key _ (localReg_pathFam_owxT3 m P.g p hp x c t hx q hq hP) Q0 hQ
    · exact key _ (localReg_pathFam_owxT4 m P.g p hp x c t hx q hq hP) Q0 hQ
  | edge p hp x v hv c t hx hwf hbad =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1EdgeOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with hQ | ⟨q, hq, T, hT, hQ⟩
    · exact key _ (localReg_pathFam_oe1xOwx m P.g p hp x c t hP) Q0 hQ
    · exact key T (localReg_pathFam_oe1xDs m P.g p hp x v c t hx q hq T hT hP) Q0 hQ
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    unfold lvl1Pack at hB
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hB
    simp only [lvl1GGOuts0, List.mem_append, List.mem_flatMap] at hQ0
    rcases hQ0 with (((((hQ | hQ) | hQ) | hQ) | hQ) | ⟨q', hq', hQ⟩) | ⟨q', hq', hQ⟩
    · exact key _ (localReg_pathFam_oe2xR2 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg_pathFam_oe2xR3 m P.g p q hp hq x c t hP) Q0 hQ
    · exact key _ (localReg_pathFam_oe2xR4 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg_pathFam_oe2xR5 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg_pathFam_oe2xR6 m P.g p q hp hq x y y' c t hp1 hq1 hP) Q0 hQ
    · exact key _ (localReg_pathFam_oe2xR7 m P.g p q hp hq x y y' c t hp1 hq1 q' hq' hP) Q0 hQ
    · exact key _ (localReg_pathFam_oe2xR8 m P.g p q hp hq x y y' c t hp1 hq1 q' hq' hP) Q0 hQ

end Assembly


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

/-- **(3) and (5)** hold for one common family of walks (`∃ W`). -/
def PGraph.LocReg35 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := ∃ W, Q.LocReg3 p W ∧ Q.LocReg5 p W

/-- **(3), (4) and (5)** hold for one common family of walks (`∃ W`): the statement of `lem:localregular` (proved in LW-10b). -/
def PGraph.LocReg345 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := ∃ W, Q.LocReg3 p W ∧ Q.LocReg4 p W ∧ Q.LocReg5 p W

/-- **(6)** the scaling order is at least `2p` (`(eq:sizeGammamu)`, `7_8:815-818`). -/
def PGraph.LocReg6 (Q : PGraph (Fin 2)) (p : ℕ) : Prop := (2 * p : ℤ) ≤ Q.g.scalingOrder

/-- **The invariant gives the walks of (3) and (5)** (the loop steps are deleted: the visited molecules do not change). -/
theorem PGraph.PathInv.exists_walks {Q : PGraph (Fin 2)} {p : ℕ} (h : Q.PathInv p) : Q.LocReg35 p := by
  obtain ⟨W, hW, hno, hB, hH⟩ := localReg_Fam.strict h
  refine ⟨W, ⟨hW, ?_⟩, hH⟩
  rw [← LGraph.localReg_offDiag_edgeMS]
  show localReg_stepMS W ≤ localReg_offDiag Q.g.localReg_edgeMS
  unfold localReg_offDiag
  refine Multiset.le_filter.2 ⟨hB, ?_⟩
  intro s hs
  unfold localReg_stepMS at hs
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hs
  obtain ⟨st, hst, rfl⟩ := localReg_mem_stepEdges.1 hi
  simpa [Sym2.mk_isDiag_iff] using hno i st hst

end Predicates

/-- **The counters of the starting graph** (`def scaling`, `(eq:initial_scaling)`, `B:201`): `n_S = 3p`, `n_W = p`, `n_V = 2p`, `n_M = p`. -/
theorem fxyPowGraph_counters (p : ℕ) :
    (fxyPowGraph p).nS = 3 * p ∧ (fxyPowGraph p).nW = p ∧ (fxyPowGraph p).nV = 2 * p ∧ (fxyPowGraph p).nM = p :=
  ⟨(localReg_fxyPowGraph_counters_aux p).1, (localReg_fxyPowGraph_counters_aux p).2.1, (localReg_fxyPowGraph_counters_aux p).2.2, fxyPowGraph_nM p⟩

/-- **`ord(Γ_p) = p`** (`(eq:initial_scaling)`, `B:201`): `2p` off-diagonal solid edges, `p` light-weights, `p` waved edges, `2p` internal vertices. -/
theorem fxyPowGraph_ord (p : ℕ) : ord (fxyPowGraph p).counters = p := by
  obtain ⟨h1, h2, h3, h4⟩ := fxyPowGraph_counters p
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

/-- The starting graph carries the path invariant. -/
theorem fxyPowGraph_pathInv (p : ℕ) : (fxyPowGraph p).pack.PathInv p := localReg_fxyPowGraph_pathFam p

/-! ## 9. The expansion theorem -/

section Expansion

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- **`lem:localregular` (first half): the local expansion of `|f_{xy}(G)|^p` and the path properties** (`7_8:786-821`, proof `B:172-199`).
`lvl1_lemma_size` for the starting graph `(fxyPowGraph p).pack` gives the lists `outs` (locally standard, of order `≥ ord Γ_p`) and `errs` (of
scaling size `≤ W^{-D}`), the expectation identity `(eq:local_Gs)`, and, for every graph of `outs`: (1) locally standard (`LocStd`), (2) `n_M ≤ p`
and `(eq:MolVW)`, (3) and (5) the `p` edge-disjoint walks with the Hall condition; for every graph of `outs ++ errs` the path invariant, which
`LW-10b` extends.  No assumption `(eq:far_ab)` is made (the walks are closed if `𝓜_x = 𝓜_y`).  Properties (4) and (6) are not part of this half. -/
theorem lw_localregular_expansion (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) :
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
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg35 p) ∧
      (∀ Q ∈ outs ++ errs, Q.PathInv p) := by
  obtain ⟨outs, errs, hA, hB, hC, hD⟩ :=
    lvl1_lemma_size (E := Fin 2) m c hc K0 d D (fxyPowGraph p).pack (fxyPowGraph_normal p)
  have hP : ∀ Q ∈ outs ++ errs, Q.PathInv p := fun Q hQ =>
    lvl1_induction (hC Q hQ).1 (fun Q : PGraph (Fin 2) => Q.PathInv p) (localReg_fxyPowGraph_pathFam p)
      (fun A L hst hA B hB => pathInv_locStep hst hA B hB)
  refine ⟨outs, errs, hA, hB, hC, hD, fun Q hQ => ?_, hP⟩
  have hQ' : Q ∈ outs ++ errs := List.mem_append_left _ hQ
  refine ⟨(hA Q hQ).1, ⟨?_, fun c => Q.g.molNV_le_molNW_add_one (hC Q hQ').2.1 c⟩, (hP Q hQ').exists_walks⟩
  have := (hC Q hQ').2.2.2.1
  rw [show (fxyPowGraph p).pack.g.nM = p from (fxyPowGraph_counters p).2.2.2] at this
  exact this

/-- **`(eq:local_Gs)` in terms of `f_{xy}`** (`7_8:790`): at the sample data of `lvl1_lemma_size` (`S = lwS` real) and `p` even, the value of the starting graph
is `f_{xy}^{p/2} \overline{f_{xy}}^{p/2} = |f_{xy}|^p` pointwise, so the expectation of `|f_{xy}(G)|^p` is that of the starting graph. -/
theorem lw_fxyPow_integral_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (u : ℝ)
    (M Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (p : ℕ) (hp : Even p)
    (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, fxyVal (lwSampleData sz n z u M (lwS sz n u) Sp ω) (ℓe 0) (ℓe 1) ^ (p / 2) *
        star (fxyVal (lwSampleData sz n z u M (lwS sz n u) Sp ω) (ℓe 0) (ℓe 1)) ^ (p / 2) ∂(Sizes.seqP sz) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [LGraph.pack_val]
  have hℓ : ℓe = ![ℓe 0, ℓe 1] := by
    funext i; fin_cases i <;> rfl
  have := fxyPowGraph_val_eq (lwSampleData sz n z u M (lwS sz n u) Sp ω) (fun i j => lwSymm_lwS_real sz n u i j) p hp
    (ℓe 0) (ℓe 1)
  rwa [← hℓ] at this

end Expansion

/-! ## 10. Compiled instances -/

section Instances

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- the data `lwD` (`LWVocab`): a generic `G`, `M = I/2`, a real symmetric `S` -/
theorem localReg_inst_lwD_S_real : ∀ i j, star (lwD.S i j) = lwD.S i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lwD]

/-- `f_{01}(G) = 259` on the data `lwD` (the single term `α = 2`; as in `LWVocab`). -/
theorem localReg_inst_lwFxyVal : fxyVal lwD 0 1 = 259 := by
  simp [fxyVal, lwD, Fin.sum_univ_three]
  norm_num

/-- **The value identity at `p = 2`** and concrete data: `|f_{01}|² = 259²`. -/
theorem localReg_inst_val2 : (fxyPowGraph 2).val lwD ![0, 1] = 67081 := by
  rw [fxyPowGraph_val_eq lwD localReg_inst_lwD_S_real 2 (by decide) 0 1, localReg_inst_lwFxyVal]
  norm_num

/-- **The value identity at `p = 4`** and concrete data: `|f_{01}|⁴ = 259⁴`. -/
theorem localReg_inst_val4 : (fxyPowGraph 4).val lwD ![0, 1] = 4499860561 := by
  rw [fxyPowGraph_val_eq lwD localReg_inst_lwD_S_real 4 (by decide) 0 1, localReg_inst_lwFxyVal]
  norm_num

/-- the counters, `ord` and normality of the starting graphs at `p = 2` and `p = 4` -/
example : (fxyPowGraph 2).nS = 3 * 2 ∧ (fxyPowGraph 2).nW = 2 ∧ (fxyPowGraph 2).nV = 2 * 2 ∧ (fxyPowGraph 2).nM = 2 :=
  fxyPowGraph_counters 2

example : ord (fxyPowGraph 2).counters = 2 := fxyPowGraph_ord 2

example : (fxyPowGraph 2).Normal := fxyPowGraph_normal 2

example : (fxyPowGraph 4).nS = 3 * 4 ∧ (fxyPowGraph 4).nW = 4 ∧ (fxyPowGraph 4).nV = 2 * 4 ∧ (fxyPowGraph 4).nM = 4 :=
  fxyPowGraph_counters 4

example : ord (fxyPowGraph 4).counters = 4 := fxyPowGraph_ord 4

example : (fxyPowGraph 4).Normal := fxyPowGraph_normal 4

example : fxyPowGraph 2 = p2Graph := fxyPowGraph_two

/-- the path invariant at the starting graphs `p = 2`, `p = 4` -/
example : (fxyPowGraph 2).pack.PathInv 2 := fxyPowGraph_pathInv 2

example : (fxyPowGraph 4).pack.PathInv 4 := fxyPowGraph_pathInv 4

/-- **`(eq:MolVW)`** at the normal graph `fxyPowGraph 4` and its molecule `{α_0, β_0}`. -/
example : (fxyPowGraph 4).molNV (localReg_fxyMol 0) ≤ (fxyPowGraph 4).molNW (localReg_fxyMol 0) + 1 :=
  LGraph.molNV_le_molNW_add_one _ (fxyPowGraph_normal 4) _

/-- **The path invariant along one `LocStep`**: Step 1 of `strat_local` at the light-weight `(Ǧ - M)_{β₁β₁}` of `p2Graph = fxyPowGraph 2`
(the merged `lvl1_inst_locStep_weight`): every output carries the invariant. -/
theorem localReg_inst_step1 :
    ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false), B.PathInv 2 :=
  pathInv_locStep lvl1_inst_locStep_weight (fxyPowGraph_pathInv 2)

/-- the predicates at the starting graph `p = 2`: (2) holds, the walks of (3) and (5) exist; (6) fails (`ord = 2 < 4`) -/
example : (fxyPowGraph 2).pack.LocReg2 2 :=
  ⟨by rw [show (fxyPowGraph 2).pack.g.nM = 2 from (fxyPowGraph_counters 2).2.2.2],
    fun c => LGraph.molNV_le_molNW_add_one _ (fxyPowGraph_normal 2) c⟩

example : (fxyPowGraph 2).pack.LocReg35 2 := (fxyPowGraph_pathInv 2).exists_walks

example : ¬ (fxyPowGraph 2).pack.LocReg6 2 := by
  unfold PGraph.LocReg6
  have : (fxyPowGraph 2).pack.g.scalingOrder = 2 := fxyPowGraph_ord 2
  omega

/-- (1) and (6) at a graph where they hold: `lvl1ExStd` is locally standard, `figGraph` has order `4 = 2p` for `p = 2` -/
example : lvl1ExStd.pack.LocReg1 := lvl1_inst_locStd_pack

example : figGraph.pack.LocReg6 2 := by
  unfold PGraph.LocReg6
  have : figGraph.pack.g.scalingOrder = 4 := figGraph_ord
  omega

/-- **No family without an edge at the start**: if `u ≠ v` and no non-loop edge of the budget contains `u`, there is no family of `p + 1` walks from `u` to `v`. -/
theorem localReg_Fam.not_of_isolated {N : Type*} {p : ℕ} {u v : N} {Int : N → Prop} {B : Multiset (Sym2 N)} (huv : u ≠ v)
    (hB : ∀ s ∈ B, s.IsDiag ∨ u ∉ s) : ¬ localReg_Fam (p + 1) u v Int B := by
  rintro ⟨W, hW, hbud, -⟩
  have hw := hW 0
  have hstep : ∀ st ∈ W 0, st.1 = st.2 ∨ s(st.1, st.2) ∈ B := by
    intro st hst
    by_cases h : st.1 = st.2
    · exact Or.inl h
    · right
      have hmem : s(st.1, st.2) ∈ localReg_stepMS W := by
        unfold localReg_stepMS
        exact Multiset.mem_sum.2 ⟨0, Finset.mem_univ _, localReg_mem_stepEdges.2 ⟨st, hst, rfl⟩⟩
      have : s(st.1, st.2) ∈ localReg_offDiag (localReg_stepMS W) := by
        unfold localReg_offDiag
        exact Multiset.mem_filter.2 ⟨hmem, by simpa [Sym2.mk_isDiag_iff] using h⟩
      exact Multiset.mem_of_le hbud this
  have key : ∀ (l : List (N × N)) (w : N), localReg_StepWalk w v l → w = u →
      (∀ st ∈ l, st.1 = st.2 ∨ s(st.1, st.2) ∈ B) → u = v := by
    intro l
    induction l with
    | nil => intro w hw hwu _; exact hwu ▸ hw
    | cons st l ih =>
      intro w hw hwu hl
      obtain ⟨a, b⟩ := st
      obtain ⟨hwa, hbv⟩ := hw
      have hl' : ∀ st ∈ l, st.1 = st.2 ∨ s(st.1, st.2) ∈ B := fun st hst => hl st (List.mem_cons_of_mem _ hst)
      by_cases hab : a = b
      · exact ih b hbv (by rw [← hab, ← hwa, hwu]) hl'
      · exfalso
        have hmem : s(a, b) ∈ B := by
          rcases hl (a, b) (List.mem_cons_self ..) with h | h
          · exact absurd h hab
          · exact h
        rcases hB _ hmem with hd | hnot
        · exact hab (Sym2.mk_isDiag_iff.1 hd)
        · exact hnot (by rw [← hwu, hwa]; exact Sym2.mem_mk_left a b)
  exact huv (key (W 0) u hw rfl hstep)

/-- A vertex without a waved or `=`-dotted edge is alone in its molecule. -/
theorem LGraph.localReg_molOf_isolated {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (v : E ⊕ I) (hv : ∀ w, Γ.adj v w = false) (w : E ⊕ I) (h : Γ.molOf v = Γ.molOf w) : w = v := by
  obtain ⟨q⟩ := SimpleGraph.ConnectedComponent.eq.1 h
  cases q with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    have := ((owx_molGraph_adj _ _ _).1 hadj).2
    rw [hv] at this
    exact absurd this (by simp)


/-- **A negative control**: the starting graph for `p = 1` without the edge `G_{xα₁}` (`x` isolated); `fxyPowGraph_pathInv 1` holds for the full graph. -/
def localReg_inst_noX : LGraph (Fin 2) (Fin 2) where
  solid := [⟨true, true, .inr 1, .inr 1⟩, ⟨true, false, .inr 0, .inl 1⟩]
  waved := [⟨false, true, .inr 0, .inr 1⟩]
  dotted := [⟨false, .inr 0, .inl 0⟩, ⟨false, .inr 0, .inl 1⟩]
  coeff := 1

/-- the path invariant fails for the graph without `G_{xα₁}`: no walk leaves the molecule of `x` -/
theorem localReg_inst_noX_not : ¬ localReg_inst_noX.pack.PathInv 1 := by
  have hiso : ∀ w, localReg_inst_noX.adj (Sum.inl 0) w = false := by decide
  have hne : ∀ w : Fin 2 ⊕ Fin 2, w ≠ Sum.inl 0 →
      localReg_inst_noX.molOf (Sum.inl 0) ≠ localReg_inst_noX.molOf w := fun w hw h =>
    hw (localReg_inst_noX.localReg_molOf_isolated _ hiso w h)
  have hE : localReg_inst_noX.localReg_edgeMS =
      ((localReg_inst_noX.solid.map fun e => s(localReg_inst_noX.molOf e.src, localReg_inst_noX.molOf e.dst) :
        List (Sym2 localReg_inst_noX.Mol)) : Multiset (Sym2 localReg_inst_noX.Mol)) := by
    unfold LGraph.localReg_edgeMS LGraph.localReg_endsMS
    rw [Multiset.map_coe, List.map_map]
    rfl
  have key : ∀ s ∈ localReg_inst_noX.localReg_edgeMS,
      s.IsDiag ∨ localReg_inst_noX.molOf (Sum.inl 0) ∉ s := by
    intro s hs
    rw [hE, Multiset.mem_coe, List.mem_map] at hs
    obtain ⟨e, he, rfl⟩ := hs
    have he' : e = ⟨true, true, Sum.inr 1, Sum.inr 1⟩ ∨ e = ⟨true, false, Sum.inr 0, Sum.inl 1⟩ := by
      simpa [localReg_inst_noX] using he
    rcases he' with rfl | rfl
    · exact Or.inl (Sym2.mk_isDiag_iff.2 rfl)
    · right
      rw [Sym2.mem_iff]
      rintro (h | h)
      · exact hne (Sum.inr 0) (by simp) h
      · exact hne (Sum.inl 1) (by simp) h
  exact localReg_Fam.not_of_isolated (p := 0) (hne (Sum.inl 1) (by simp)) key

/-- **`lw_localregular_expansion` at `p = 2`**, `d = 3`, `c = 1/4`, `K0 = 1` (`L^3 ≤ W`), `D = 10`; the regime is evaluated at `W = 27`, `L = 3`,
`Ψ = 27^{-1/4}`; the expectation identity holds at the merged instance data of `Graph/LWWeightExp.lean` (`lwWxInstSz`: `d = 3`, `L = 3`, `W = 1`, `m = i`,
`z = zt 0 (1/2)`, `u = 1/2`) with every hypothesis discharged (`GaussIBP` is the proved `gaussIBP`). -/
theorem localReg_inst_expansion :
    ∃ outs errs : List (PGraph (Fin 2)),
      (∀ Q ∈ outs, Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ errs, Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
      ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
          (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum ∧
      (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg35 2) ∧
      (∀ Q ∈ outs ++ errs, Q.PathInv 2) := by
  obtain ⟨outs, errs, h1, h2, -, hid, h5, h6⟩ :=
    lw_localregular_expansion 2 (mE 0) (1 / 4) (by norm_num) 1 3 10
  refine ⟨outs, errs, fun Q hQ => ?_, fun Q hQ => ?_, ?_, h5, h6⟩
  · obtain ⟨a, b⟩ := h1 Q hQ
    have e : (fxyPowGraph 2).pack.g.scalingOrder = 2 := fxyPowGraph_ord 2
    exact ⟨a, by rw [e] at b; exact b⟩
  · refine h2 Q hQ 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_ (le_refl _)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · exact hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) (lwWx_mE_ne 0 lwWx_inst_hE)
      (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 lwSymmInstL

/-- **`(eq:local_Gs)` with `|f_{xy}|^p`** at the same data: the integrand of the left-hand side is `f_{xy}^{p/2} \overline{f_{xy}}^{p/2}` (`p = 2`). -/
example :
    ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      ∫ ω, fxyVal (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω)
          (lwSymmInstL 0) (lwSymmInstL 1) ^ (2 / 2) *
        star (fxyVal (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω)
          (lwSymmInstL 0) (lwSymmInstL 1)) ^ (2 / 2) ∂(Sizes.seqP lwWxInstSz) :=
  lw_fxyPow_integral_eq lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM lwWxInstSp 2 (by decide) lwSymmInstL

end Instances

end RBM.Graph
end
