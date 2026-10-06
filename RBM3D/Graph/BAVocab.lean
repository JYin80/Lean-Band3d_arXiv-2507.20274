/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWVocab
import Mathlib.Logic.Relation

/-!
# BA-L1: the graph vocabulary of the block Anderson model (T2287)

The vocabulary of `paper/tex/B_graphical_lemmas.tex:286-356` (cited `B:line`) on top of the merged
record `LGraph` (`RBM3D/Graph/LWVocab.lean`, DECISIONS §24, representation A).  A block Anderson
graph `BAGraph` is an `LGraph` with `Ψ`-dotted and `M`-dotted edges (`B:290-297`).  Defined here:
its atoms (`def_atom`, `B:302-304`), molecules (`B:299`), normal graphs (`defn_normalBA`,
`B:331-343`), the partition (`G = Ǧ + M`, then the merge of the `=`-dotted classes, `B:339-341`) and
the scaling size and order (`def scalingBA`, `B:345-356`).

The vocabulary section is copied verbatim from `docs/tickets/checks/T2287-check.lean` section 2.
Delta candidates: T2287a ("regular dotted" is `=`-dotted: the `×`-dotted edges do not join atoms),
T2287b (`Ψ`- and `M`-dotted edges join molecules).  No hypothesis on the data `BALData` is needed
for the value identities (`G = (G - M) + M` is literal in `SEdge.val`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ## 1. The vocabulary (copied verbatim from the check file, section 2) -/

namespace RBM.Graph

/-- The matrices a block Anderson graph reads: those of `LData` (`M` is the matrix
`Mres ((g : ℂ) • PsiI d L W) z m`, not `m I`) and `gPsi`, the matrix `ilambda Ψ` of `(eq:Psi3D)`
(`1_2:614-616`): a `Ψ`-dotted edge `x — y` is the factor `gPsi x y` (`B:293`). -/
structure BALData (ι : Type*) extends RBM.Graph.LData ι where
  gPsi : Matrix ι ι ℂ

/-- A `Ψ`-dotted edge (`B:293`): the factor `ilambda Ψ_{xy}`. -/
structure BAPsiEdge (V : Type*) where
  x : V
  y : V

/-- An `M`-dotted edge (`B:295`): blue (`σ = true`) `M_{xy}`, red (`σ = false`) `M̄_{xy}`. -/
structure BAMEdge (V : Type*) where
  σ : Bool
  x : V
  y : V

/-- A **block Anderson graph** (`B:290-297`): a graph of `def_graph1` (the merged record) with
`Ψ`-dotted and `M`-dotted edges. -/
structure BAGraph (E I : Type*) extends RBM.Graph.LGraph E I where
  psi : List (BAPsiEdge (E ⊕ I))
  mdot : List (BAMEdge (E ⊕ I))

def BAPsiEdge.map {V W : Type*} (f : V → W) (e : BAPsiEdge V) : BAPsiEdge W := ⟨f e.x, f e.y⟩

def BAMEdge.map {V W : Type*} (f : V → W) (e : BAMEdge V) : BAMEdge W := ⟨e.σ, f e.x, f e.y⟩

/-- The factor of a `Ψ`-dotted edge at the labelling `ℓ`. -/
def BAPsiEdge.val {ι V : Type*} (D : BALData ι) (ℓ : V → ι) (e : BAPsiEdge V) : ℂ :=
  D.gPsi (ℓ e.x) (ℓ e.y)

/-- The factor of an `M`-dotted edge at the labelling `ℓ`. -/
noncomputable def BAMEdge.val {ι V : Type*} (D : BALData ι) (ℓ : V → ι) (e : BAMEdge V) : ℂ :=
  if e.σ then D.M (ℓ e.x) (ℓ e.y) else star (D.M (ℓ e.x) (ℓ e.y))

/-- The product of all edge factors and the coefficient at a labelling of all vertices. -/
noncomputable def BAGraph.term {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓ : E ⊕ I → ι) : ℂ :=
  Γ.toLGraph.term D.toLData ℓ * (Γ.psi.map (BAPsiEdge.val D ℓ)).prod *
    (Γ.mdot.map (BAMEdge.val D ℓ)).prod

/-- `ValG` (`7_8:159-164`) for block Anderson graphs: the internal labels are summed. -/
noncomputable def BAGraph.val {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) : ℂ :=
  ∑ ℓi : I → ι, Γ.term D (Sum.elim ℓe ℓi)

/-- A graph of `def_graph1` read as a block Anderson graph (no `Ψ`- or `M`-dotted edges). -/
def BAGraph.ofLGraph {E I : Type*} (Γ : RBM.Graph.LGraph E I) : BAGraph E I :=
  BAGraph.mk Γ [] []

/-- `Γ` with one more `M`-dotted edge. -/
def BAGraph.addM {E I : Type*} (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) : BAGraph E I :=
  BAGraph.mk Γ.toLGraph Γ.psi (e :: Γ.mdot)

/-- `u`, `v` are joined by a `=`-dotted, a `Ψ`-dotted or an `M`-dotted edge (`def_atom`, `B:303`; the
`×`-dotted edges do not join atoms, delta candidate T2287a). -/
def BAGraph.atomAdj {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (u v : E ⊕ I) : Bool :=
  Γ.dotted.any (fun e => e.eq && decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) ||
  Γ.psi.any (fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) ||
  Γ.mdot.any (fun e => decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)))

/-- One step of the atom closure. -/
def BAGraph.atomStep {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (s : Finset (E ⊕ I)) : Finset (E ⊕ I) :=
  s ∪ Finset.univ.filter (fun w => ∃ v ∈ s, Γ.atomAdj v w = true)

/-- **The atom of `v`** (`def_atom`, `B:302-304`): the closure of `{v}` under the dotted edges of the
three kinds (`|E ⊕ I|` steps reach the fixed point). -/
def BAGraph.atom {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v : E ⊕ I) : Finset (E ⊕ I) :=
  (Γ.atomStep)^[Fintype.card (E ⊕ I)] {v}

/-- `n_A`: the number of internal atoms (atoms without an external vertex; `B:304`, `B:351`). -/
def BAGraph.nA {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : ℕ :=
  ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)).image Γ.atom).card

/-- Molecules of a block Anderson graph (`def_poly`, `7_8:172`, "remain the same", `B:299`): waved
edges and dotted edges of all three kinds (delta candidate T2287b). -/
def BAGraph.adj {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (u v : E ⊕ I) : Bool :=
  Γ.toLGraph.adj u v || Γ.atomAdj u v

def BAGraph.step {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (s : Finset (E ⊕ I)) : Finset (E ⊕ I) :=
  s ∪ Finset.univ.filter (fun w => ∃ v ∈ s, Γ.adj v w = true)

/-- The molecule of `v`. -/
def BAGraph.mol {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v : E ⊕ I) : Finset (E ⊕ I) :=
  (Γ.step)^[Fintype.card (E ⊕ I)] {v}

/-- `n_M`: the number of internal molecules. -/
def BAGraph.nM {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : ℕ :=
  ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.mol v, w.isRight = true)).image Γ.mol).card

/-- `n_S`: solid edges (light-weights included). -/
def BAGraph.nS {E I : Type*} (Γ : BAGraph E I) : ℕ := Γ.solid.length

/-- `n_W`: waved edges. -/
def BAGraph.nW {E I : Type*} (Γ : BAGraph E I) : ℕ := Γ.waved.length

/-- The counters of `def scalingBA` (`B:349-353`) in the merged `Counters`: the slot `nV` holds `n_A`. -/
def BAGraph.counters {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : RBM.Graph.Counters :=
  ⟨Γ.nS, Γ.nW, Γ.nA, Γ.nM, 0, 0⟩

/-- `(eq:ordG_BA)` (`B:353`): `ord(Γ) = n_S + 2 (n_W - n_A)`, the merged `ord` of the counters. -/
def BAGraph.scalingOrder {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : ℤ :=
  RBM.Graph.ord Γ.counters

/-- `(eq_defsize_BA)` (`B:349-350`): `size(Γ) = (L^d)^{n_M} Ψ^{n_S} W^{-d (n_W - n_A)}`. -/
noncomputable def BAGraph.scalingSize {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  Γ.counters.scalingSize Ψ W d L

/-- **Normal** (`defn_normalBA`, `B:331-343`): (ii) no `=`-dotted edge (`Ψ`-, `M`- and `×`-dotted edges
allowed; reading of "regular dotted", delta candidate T2287a); (iii) every solid edge carries a circle.
(i) is not a property of a record (as `LGraph.Normal`, `LWVocab.lean:981-989`). -/
def BAGraph.Normal {E I : Type*} (Γ : BAGraph E I) : Prop :=
  (∀ e ∈ Γ.dotted, e.eq = false) ∧ (∀ e ∈ Γ.solid, e.circ = true)

/-- `G_{xy} = Ǧ_{xy} + M_{xy}` (resp. `Ḡ_{xy} = \overline{Ǧ_{xy}} + M̄_{xy}`) on every solid edge without a
circle (`B:339-340`): the list of (solid edges, new `M`-dotted edges) of the terms. -/
def baSplitSolid {V : Type*} : List (RBM.Graph.SEdge V) → List (List (RBM.Graph.SEdge V) × List (BAMEdge V))
  | [] => [([], [])]
  | e :: es => (baSplitSolid es).flatMap fun r =>
      if e.circ then [(e :: r.1, r.2)]
      else [(RBM.Graph.SEdge.mk e.σ true e.src e.dst :: r.1, r.2), (r.1, BAMEdge.mk e.σ e.src e.dst :: r.2)]

/-- The terms of the `G = Ǧ + M` expansion of `Γ` (`B:339-340`). -/
def BAGraph.splitG {E I : Type*} (Γ : BAGraph E I) : List (BAGraph E I) :=
  (baSplitSolid Γ.solid).map fun r =>
    BAGraph.mk (RBM.Graph.LGraph.mk r.1 Γ.waved Γ.dotted Γ.coeff) Γ.psi (r.2 ++ Γ.mdot)

/-- A block Anderson graph with its own vertex types and the map of the external vertices (the BA
twin of the merged `PGraph`, `LWVocab.lean:653`). -/
structure BAPGraph (E : Type) where
  E' : Type
  I' : Type
  [instFE : Fintype E']
  [instDE : DecidableEq E']
  [instFI : Fintype I']
  [instDI : DecidableEq I']
  ext : E → E'
  ext_surj : Function.Surjective ext
  g : BAGraph E' I'

/-- The value of a packed graph (as `PGraph.val`, `LWVocab.lean:673`). -/
noncomputable def BAPGraph.val {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E)
    (D : BALData ι) (ℓe : E → ι) : ℂ :=
  letI := P.instFI
  letI := P.instDI
  open Classical in
  if h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext then P.g.val D h.choose else 0

/-- The counters of a packed graph. -/
noncomputable def BAPGraph.counters {E : Type} (P : BAPGraph E) : RBM.Graph.Counters :=
  letI := P.instFE
  letI := P.instDE
  letI := P.instFI
  letI := P.instDI
  P.g.counters

noncomputable def BAPGraph.scalingOrder {E : Type} (P : BAPGraph E) : ℤ := RBM.Graph.ord P.counters

noncomputable def BAPGraph.scalingSize {E : Type} (P : BAPGraph E) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  P.counters.scalingSize Ψ W d L

/-- The value of a linear combination of packed graphs. -/
noncomputable def BAComb.val {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (L : List (BAPGraph E))
    (D : BALData ι) (ℓe : E → ι) : ℂ :=
  (L.map fun P => P.val D ℓe).sum

/-- Merging the vertices joined by `=`-dotted edges (`B:340`; the merged `LGraph.merge`, `LWVocab.lean:778`,
on the underlying graph; the `Ψ`- and `M`-dotted edges are carried along `vmap`). -/
noncomputable def BAGraph.merge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : BAGraph Γ.toLGraph.ExtCls Γ.toLGraph.IntCls :=
  BAGraph.mk Γ.toLGraph.merge (Γ.psi.map (BAPsiEdge.map Γ.toLGraph.vmap))
    (Γ.mdot.map (BAMEdge.map Γ.toLGraph.vmap))

noncomputable def BAGraph.packMerge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : BAPGraph E where
  E' := Γ.toLGraph.ExtCls
  I' := Γ.toLGraph.IntCls
  ext := Γ.toLGraph.extMap
  ext_surj := Γ.toLGraph.extMap_surj
  g := Γ.merge

/-- **The BA partition** (`B:339-341`): the terms of `G = Ǧ + M`, each with the `=`-dotted classes merged. -/
noncomputable def BAGraph.partition {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : List (BAPGraph E) :=
  Γ.splitG.map BAGraph.packMerge

/-- `ord` of a general graph (`B:354-355`): the minimum over the partition (`⊤` if empty). -/
noncomputable def BAGraph.scalingOrderG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : WithTop ℤ :=
  (Γ.partition.map fun P => ((P.scalingOrder : ℤ) : WithTop ℤ)).foldr min ⊤

/-- `size` of a general graph (`B:354`, `(eq_defsizemax)`): the maximum over the partition (`0` if empty). -/
noncomputable def BAGraph.scalingSizeG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (Ψ : ℝ) (W d L : ℕ) : ℝ :=
  (Γ.partition.map fun P => P.scalingSize Ψ W d L).foldr max 0

attribute [instance] BAPGraph.instFE BAPGraph.instDE BAPGraph.instFI BAPGraph.instDI

/-! ## 3. Value (`B:290-297`): `ofLGraph` and `addM` -/

/-- A graph of `def_graph1` read as a block Anderson graph has its own value. -/
theorem BAGraph.val_ofLGraph {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : RBM.Graph.LGraph E I) (D : BALData ι) (ℓe : E → ι) :
    (BAGraph.ofLGraph Γ).val D ℓe = Γ.val D.toLData ℓe := by
  simp [BAGraph.val, BAGraph.term, BAGraph.ofLGraph, RBM.Graph.LGraph.val]

/-- An `M`-dotted edge multiplies the term by its factor. -/
theorem BAGraph.term_addM {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (e : BAMEdge (E ⊕ I)) (D : BALData ι) (ℓ : E ⊕ I → ι) :
    (Γ.addM e).term D ℓ = Γ.term D ℓ * e.val D ℓ := by
  simp only [BAGraph.term, BAGraph.addM, List.map_cons, List.prod_cons]
  ring

/-! ## 4. Atoms and molecules (`B:299-304`): the closure is the reflexive-transitive closure -/

section Closure

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One step of the neighbourhood closure of a (Boolean) relation. -/
private def BAVocab_step (r : α → α → Bool) (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter (fun w => ∃ v ∈ s, r v w = true)

private theorem BAVocab_subset_step (r : α → α → Bool) (s : Finset α) : s ⊆ BAVocab_step r s :=
  Finset.subset_union_left

private theorem BAVocab_step_mono (r : α → α → Bool) : Monotone (BAVocab_step r) := by
  intro s t h w hw
  simp only [BAVocab_step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with hw | ⟨v, hv, hadj⟩
  · exact Or.inl (h hw)
  · exact Or.inr ⟨v, h hv, hadj⟩

private theorem BAVocab_subset_iterate (r : α → α → Bool) (n : ℕ) (s : Finset α) :
    s ⊆ (BAVocab_step r)^[n] s := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (BAVocab_subset_step r _)

private theorem BAVocab_iterate_mono_nat (r : α → α → Bool) {n m : ℕ} (h : n ≤ m) (s : Finset α) :
    (BAVocab_step r)^[n] s ⊆ (BAVocab_step r)^[m] s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact BAVocab_subset_iterate r k _

/-- The graph of a symmetric relation. -/
private def BAVocab_graph (r : α → α → Bool) : SimpleGraph α :=
  SimpleGraph.fromRel fun u v => r u v = true

private theorem BAVocab_graph_adj (r : α → α → Bool) (hs : ∀ u v, r u v = r v u) (u v : α) :
    (BAVocab_graph r).Adj u v ↔ u ≠ v ∧ r u v = true := by
  simp only [BAVocab_graph, SimpleGraph.fromRel_adj, hs v u, or_self]

private theorem BAVocab_reachable_of_mem_iterate (r : α → α → Bool) (hs : ∀ u v, r u v = r v u)
    (n : ℕ) : ∀ (v w : α), w ∈ (BAVocab_step r)^[n] {v} → (BAVocab_graph r).Reachable v w := by
  induction n with
  | zero =>
    intro v w h
    simp only [Function.iterate_zero, id, Finset.mem_singleton] at h
    subst h; exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    intro v w h
    rw [Function.iterate_succ_apply'] at h
    simp only [BAVocab_step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | ⟨u, hu, hadj⟩
    · exact ih v w h
    · have h1 := ih v u hu
      by_cases huw : u = w
      · subst huw; exact h1
      · exact h1.trans (SimpleGraph.Adj.reachable ((BAVocab_graph_adj r hs u w).2 ⟨huw, hadj⟩))

private theorem BAVocab_walk_mem_iterate (r : α → α → Bool) (hs : ∀ u v, r u v = r v u) {v w : α}
    (p : (BAVocab_graph r).Walk v w) : w ∈ (BAVocab_step r)^[p.length] {v} := by
  induction p with
  | nil => simp
  | @cons u v' w' h p ih =>
    rw [SimpleGraph.Walk.length_cons, Function.iterate_succ_apply]
    refine ((BAVocab_step_mono r).iterate p.length) ?_ ih
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp only [BAVocab_step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact Or.inr ⟨u, rfl, ((BAVocab_graph_adj r hs u x).1 h).2⟩

private theorem BAVocab_reflTransGen_iff_reachable (r : α → α → Bool) (hs : ∀ u v, r u v = r v u)
    (v w : α) : Relation.ReflTransGen (fun a b => r a b = true) v w ↔
      (BAVocab_graph r).Reachable v w := by
  constructor
  · intro h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ hbc ih =>
      by_cases hbc' : b = c
      · subst hbc'; exact ih
      · exact ih.trans (SimpleGraph.Adj.reachable ((BAVocab_graph_adj r hs b c).2 ⟨hbc', hbc⟩))
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    refine Relation.ReflTransGen.mono ?_ v w h
    intro a b hab
    exact ((BAVocab_graph_adj r hs a b).1 hab).2

/-- The closure of `{v}` under a symmetric relation after `|α|` steps is the reflexive-transitive
closure. -/
private theorem BAVocab_mem_iterate_iff (r : α → α → Bool) (hs : ∀ u v, r u v = r v u) (v w : α) :
    w ∈ (BAVocab_step r)^[Fintype.card α] {v} ↔
      Relation.ReflTransGen (fun a b => r a b = true) v w := by
  rw [BAVocab_reflTransGen_iff_reachable r hs]
  constructor
  · exact BAVocab_reachable_of_mem_iterate r hs _ v w
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    exact BAVocab_iterate_mono_nat r hp.length_lt.le _ (BAVocab_walk_mem_iterate r hs p)

private theorem BAVocab_rtg_symm (r : α → α → Bool) (hs : ∀ u v, r u v = r v u) {v w : α}
    (h : Relation.ReflTransGen (fun a b => r a b = true) v w) :
    Relation.ReflTransGen (fun a b => r a b = true) w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (by rw [hs]; exact hbc) ih

end Closure

section AtomMol

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAVocab_atomAdj_comm (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.atomAdj u v = Γ.atomAdj v u := by
  simp only [BAGraph.atomAdj, or_comm]

private theorem BAVocab_ladj_comm (Γ : RBM.Graph.LGraph E I) (u v : E ⊕ I) :
    Γ.adj u v = Γ.adj v u := by
  simp only [RBM.Graph.LGraph.adj, or_comm]

private theorem BAVocab_adj_comm (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [BAGraph.adj, BAVocab_ladj_comm Γ.toLGraph u v, BAVocab_atomAdj_comm Γ u v]

/-- The atom of `v` (`def_atom`, `B:302-304`) is the set of vertices reachable by `=`-, `Ψ`- and
`M`-dotted edges. -/
theorem BAGraph.mem_atom_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v w : E ⊕ I) :
    w ∈ Γ.atom v ↔ Relation.ReflTransGen (fun a b => Γ.atomAdj a b = true) v w :=
  BAVocab_mem_iterate_iff (fun a b => Γ.atomAdj a b) (BAVocab_atomAdj_comm Γ) v w

/-- The molecule of `v` (`def_poly`, `B:299`) is the set of vertices reachable by waved and dotted
edges of all three kinds. -/
theorem BAGraph.mem_mol_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v w : E ⊕ I) :
    w ∈ Γ.mol v ↔ Relation.ReflTransGen (fun a b => Γ.adj a b = true) v w :=
  BAVocab_mem_iterate_iff (fun a b => Γ.adj a b) (BAVocab_adj_comm Γ) v w

/-- Atoms lie inside molecules (`B:299`). -/
theorem BAGraph.atom_subset_mol {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (v : E ⊕ I) : Γ.atom v ⊆ Γ.mol v := by
  intro w hw
  rw [BAGraph.mem_atom_iff] at hw
  rw [BAGraph.mem_mol_iff]
  refine Relation.ReflTransGen.mono ?_ v w hw
  intro a b hab
  simp [BAGraph.adj, hab]

private theorem BAVocab_atom_eq_of_mem (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.atom v) :
    Γ.atom w = Γ.atom v := by
  rw [BAGraph.mem_atom_iff] at h
  ext x
  rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx; exact (BAVocab_rtg_symm (fun a b => Γ.atomAdj a b) (BAVocab_atomAdj_comm Γ) h).trans hx

private theorem BAVocab_mol_eq_of_mem (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.mol v) :
    Γ.mol w = Γ.mol v := by
  rw [BAGraph.mem_mol_iff] at h
  ext x
  rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx; exact (BAVocab_rtg_symm (fun a b => Γ.adj a b) (BAVocab_adj_comm Γ) h).trans hx

/-- Every vertex lies in its own atom. -/
private theorem BAVocab_self_mem_atom (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.atom v := by
  rw [BAGraph.mem_atom_iff]

private theorem BAVocab_self_mem_mol (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.mol v := by
  rw [BAGraph.mem_mol_iff]

/-- The number of internal atoms is at most the number of internal vertices. -/
theorem BAGraph.nA_le_card {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : Γ.nA ≤ Fintype.card I := by
  unfold BAGraph.nA
  set T : Finset (E ⊕ I) := Finset.univ.filter
    (fun v => (∀ w ∈ Γ.atom v, w.isRight = true) ∧ v.isRight = true) with hT
  have himg : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)).image Γ.atom
      ⊆ T.image Γ.atom := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine Finset.mem_image.2 ⟨v, ?_, rfl⟩
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv, hv v (BAVocab_self_mem_atom Γ v)⟩
  have hTsub : T ⊆ Finset.univ.image (Sum.inr : I → E ⊕ I) := by
    intro v hv
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases v with a | b
    · simp at hv
    · exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩
  calc _ ≤ (T.image Γ.atom).card := Finset.card_le_card himg
    _ ≤ T.card := Finset.card_image_le
    _ ≤ (Finset.univ.image (Sum.inr : I → E ⊕ I)).card := Finset.card_le_card hTsub
    _ = Fintype.card I := by
      rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]

/-- The number of internal molecules is at most the number of internal atoms: an internal molecule is a
union of atoms. -/
theorem BAGraph.nM_le_nA {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) : Γ.nM ≤ Γ.nA := by
  classical
  unfold BAGraph.nM BAGraph.nA
  set F : Finset (E ⊕ I) → Finset (E ⊕ I) := fun A =>
    if h : A.Nonempty then Γ.mol h.choose else ∅ with hF
  have hFa : ∀ v, F (Γ.atom v) = Γ.mol v := by
    intro v
    have hne : (Γ.atom v).Nonempty := ⟨v, BAVocab_self_mem_atom Γ v⟩
    simp only [hF, hne, ↓reduceDIte]
    exact BAVocab_mol_eq_of_mem Γ (Γ.atom_subset_mol v hne.choose_spec)
  have hsub : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.mol v, w.isRight = true)).image Γ.mol ⊆
      ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)).image Γ.atom).image F := by
    intro T hT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine Finset.mem_image.2 ⟨Γ.atom v, Finset.mem_image.2 ⟨v, ?_, rfl⟩, hFa v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun w hw => hv w (Γ.atom_subset_mol v hw)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end AtomMol

/-! ## 5. Scaling size and the bridge to the vertex-level graphs (`B:318-320`, `B:345-353`) -/

section Scaling

/-- The identity of `7_8:274-275` with `n_A` in place of `n_V`:
`size(Γ) = (L^d)^{n_M} Ψ^{ord(Γ)} (W^d Ψ²)^{n_A - n_W}`. -/
theorem BAGraph.scalingSize_eq {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) {Ψ : ℝ} (W d L : ℕ) (hΨ : Ψ ≠ 0) :
    Γ.scalingSize Ψ W d L =
      ((L : ℝ) ^ d) ^ Γ.nM * Ψ ^ Γ.scalingOrder * ((W : ℝ) ^ d * Ψ ^ 2) ^ ((Γ.nA : ℤ) - Γ.nW) := by
  unfold BAGraph.scalingSize BAGraph.scalingOrder
  exact Counters.scalingSize_eq _ W d L hΨ

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAVocab_atomAdj_ofL (Γ : RBM.Graph.LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false)
    (u v : E ⊕ I) : (BAGraph.ofLGraph Γ).atomAdj u v = false := by
  simp only [BAGraph.atomAdj, BAGraph.ofLGraph, List.any_nil, Bool.or_false]
  rw [Bool.eq_false_iff]
  intro hh
  simp only [List.any_eq_true, Bool.and_eq_true] at hh
  obtain ⟨e, he, he1, _⟩ := hh
  rw [h e he] at he1
  exact absurd he1 (by simp)

private theorem BAVocab_atom_ofL (Γ : RBM.Graph.LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false)
    (v : E ⊕ I) : (BAGraph.ofLGraph Γ).atom v = {v} := by
  ext w
  rw [BAGraph.mem_atom_iff, Finset.mem_singleton]
  constructor
  · intro hw
    induction hw with
    | refl => rfl
    | @tail b c _ hbc ih =>
      rw [BAVocab_atomAdj_ofL Γ h] at hbc
      exact absurd hbc (by simp)
  · rintro rfl; exact Relation.ReflTransGen.refl

private theorem BAVocab_card_isRight : (Finset.univ.filter (fun v : E ⊕ I => v.isRight = true)).card =
    Fintype.card I := by
  have : (Finset.univ.filter (fun v : E ⊕ I => v.isRight = true)) =
      Finset.univ.image (Sum.inr : I → E ⊕ I) := by
    ext v
    rcases v with a | b <;> simp
  rw [this, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]

/-- Without `=`-dotted edges every atom is a vertex, and the counters of the block Anderson reading of
a graph of `def_graph1` are its counters (`B:318-320`). -/
theorem BAGraph.counters_ofLGraph {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : RBM.Graph.LGraph E I) :
    (∀ e ∈ Γ.dotted, e.eq = false) → (BAGraph.ofLGraph Γ).counters = Γ.counters := by
  intro h
  have hA : (BAGraph.ofLGraph Γ).nA = Fintype.card I := by
    unfold BAGraph.nA
    have hf : (BAGraph.ofLGraph Γ).atom = fun v => {v} := funext (BAVocab_atom_ofL Γ h)
    rw [hf]
    simp only [Finset.mem_singleton, forall_eq]
    rw [Finset.card_image_of_injective _ Finset.singleton_injective]
    exact BAVocab_card_isRight
  have hadj : ∀ u v, (BAGraph.ofLGraph Γ).adj u v = Γ.adj u v := by
    intro u v
    change (Γ.adj u v || (BAGraph.ofLGraph Γ).atomAdj u v) = Γ.adj u v
    rw [BAVocab_atomAdj_ofL Γ h, Bool.or_false]
  have hstep : (BAGraph.ofLGraph Γ).step = Γ.step := by
    funext s
    simp only [BAGraph.step, RBM.Graph.LGraph.step, hadj]
  have hmol : (BAGraph.ofLGraph Γ).mol = Γ.mol := by
    funext v
    simp only [BAGraph.mol, RBM.Graph.LGraph.mol, hstep]
  have hM : (BAGraph.ofLGraph Γ).nM = Γ.nM := by
    unfold BAGraph.nM RBM.Graph.LGraph.nM
    rw [hmol]
  unfold BAGraph.counters RBM.Graph.LGraph.counters
  rw [hA, hM]
  rfl

/-- The scaling order of the block Anderson reading of a graph of `def_graph1` without `=`-dotted
edges is its scaling order. -/
theorem BAGraph.scalingOrder_ofLGraph {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : RBM.Graph.LGraph E I) :
    (∀ e ∈ Γ.dotted, e.eq = false) → (BAGraph.ofLGraph Γ).scalingOrder = Γ.scalingOrder := by
  intro h
  unfold BAGraph.scalingOrder RBM.Graph.LGraph.scalingOrder
  rw [BAGraph.counters_ofLGraph Γ h]

end Scaling

/-! ## 6. `G = Ǧ + M` on every solid edge (`B:339-340`) -/

section Split

private theorem BAVocab_sum_comm {α β : Type*} [Fintype α] (l : List β) (f : α → β → ℂ) :
    ∑ x, (l.map fun c => f x c).sum = (l.map fun c => ∑ x, f x c).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp [Finset.sum_add_distrib, ih]

private theorem BAVocab_sum_flatMap {α β : Type*} [AddCommMonoid β] (a : List α) (g : α → List β) :
    (a.flatMap g).sum = (a.map fun x => (g x).sum).sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem BAVocab_split_props {V : Type*} (es : List (SEdge V)) :
    ∀ r ∈ baSplitSolid es, (∀ e ∈ r.1, e.circ = true) ∧ r.1.length + r.2.length = es.length := by
  induction es with
  | nil =>
    intro r hr
    simp only [baSplitSolid, List.mem_singleton] at hr
    subst hr
    simp
  | cons e es ih =>
    intro r hr
    simp only [baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r', hr', hr⟩ := hr
    obtain ⟨h1, h2⟩ := ih r' hr'
    cases hc : e.circ
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨?_, by simp [h2.symm]; omega⟩
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · rfl
        · exact h1 e' he'
      · exact ⟨h1, by simp; omega⟩
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      refine ⟨?_, by simp; omega⟩
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hc
      · exact h1 e' he'

private theorem BAVocab_split_val {ι V : Type*} (D : BALData ι) (ℓ : V → ι) (es : List (SEdge V)) :
    ((baSplitSolid es).map fun r => (r.1.map (SEdge.val D.toLData ℓ)).prod *
        (r.2.map (BAMEdge.val D ℓ)).prod).sum = (es.map (SEdge.val D.toLData ℓ)).prod := by
  induction es with
  | nil => simp [baSplitSolid]
  | cons e es ih =>
    set F : List (SEdge V) × List (BAMEdge V) → ℂ := fun r => (r.1.map (SEdge.val D.toLData ℓ)).prod *
        (r.2.map (BAMEdge.val D ℓ)).prod with hF
    have key : ∀ r ∈ baSplitSolid es,
        ((if e.circ then [(e :: r.1, r.2)] else
          [(SEdge.mk e.σ true e.src e.dst :: r.1, r.2), (r.1, BAMEdge.mk e.σ e.src e.dst :: r.2)]).map
            F).sum = SEdge.val D.toLData ℓ e * F r := by
      intro r _
      obtain ⟨σ, c, s, d⟩ := e
      cases c
      · have hval : SEdge.val D.toLData ℓ ⟨σ, true, s, d⟩ + BAMEdge.val D ℓ ⟨σ, s, d⟩ =
            SEdge.val D.toLData ℓ ⟨σ, false, s, d⟩ := by
          cases σ <;> simp [SEdge.val, BAMEdge.val, star_sub]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, hF, List.prod_cons]
        rw [← hval]
        ring
      · simp [hF, mul_assoc]
    simp only [baSplitSolid]
    rw [List.map_flatMap, BAVocab_sum_flatMap, List.map_congr_left key, List.sum_map_mul_left, ih]
    simp [List.prod_cons]

/-- **`G = Ǧ + M` on every solid edge without circle** (`B:339-340`): the sum of the values of the terms
`splitG` is the value of the graph.  No hypothesis on the data `D` is needed. -/
theorem BAGraph.val_splitG {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) :
    (Γ.splitG.map fun Δ => Δ.val D ℓe).sum = Γ.val D ℓe := by
  have hterm : ∀ (r : List (SEdge (E ⊕ I)) × List (BAMEdge (E ⊕ I))) (ℓ : E ⊕ I → ι),
      (BAGraph.mk (RBM.Graph.LGraph.mk r.1 Γ.waved Γ.dotted Γ.coeff) Γ.psi (r.2 ++ Γ.mdot)).term D ℓ =
        (Γ.coeff * (Γ.waved.map (WEdge.val D.toLData ℓ)).prod * (Γ.dotted.map (DEdge.val ℓ)).prod *
          (Γ.psi.map (BAPsiEdge.val D ℓ)).prod * (Γ.mdot.map (BAMEdge.val D ℓ)).prod) *
        ((r.1.map (SEdge.val D.toLData ℓ)).prod * (r.2.map (BAMEdge.val D ℓ)).prod) := by
    intro r ℓ
    simp only [BAGraph.term, RBM.Graph.LGraph.term, List.map_append, List.prod_append]
    ring
  calc (Γ.splitG.map fun Δ => Δ.val D ℓe).sum
      = ((baSplitSolid Γ.solid).map fun r => ∑ ℓi : I → ι,
          (Γ.coeff * (Γ.waved.map (WEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
            (Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod *
            (Γ.psi.map (BAPsiEdge.val D (Sum.elim ℓe ℓi))).prod *
            (Γ.mdot.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod) *
          ((r.1.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
            (r.2.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod)).sum := by
        simp only [BAGraph.splitG, List.map_map, Function.comp_def, BAGraph.val, hterm]
    _ = ∑ ℓi : I → ι, ((baSplitSolid Γ.solid).map fun r =>
          (Γ.coeff * (Γ.waved.map (WEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
            (Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod *
            (Γ.psi.map (BAPsiEdge.val D (Sum.elim ℓe ℓi))).prod *
            (Γ.mdot.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod) *
          ((r.1.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
            (r.2.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod)).sum :=
        (BAVocab_sum_comm (baSplitSolid Γ.solid) fun ℓi r =>
          (Γ.coeff * (Γ.waved.map (WEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
            (Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod *
            (Γ.psi.map (BAPsiEdge.val D (Sum.elim ℓe ℓi))).prod *
            (Γ.mdot.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod) *
          ((r.1.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
            (r.2.map (BAMEdge.val D (Sum.elim ℓe ℓi))).prod)).symm
    _ = Γ.val D ℓe := by
        refine Finset.sum_congr rfl fun ℓi _ => ?_
        rw [List.sum_map_mul_left, BAVocab_split_val]
        simp only [BAGraph.term, RBM.Graph.LGraph.term]
        ring

/-- Every solid edge of a term of `splitG` carries a circle. -/
theorem BAGraph.splitG_circ {E I : Type} (Γ : BAGraph E I) :
    ∀ Δ ∈ Γ.splitG, ∀ e ∈ Δ.solid, e.circ = true := by
  intro Δ hΔ e he
  simp only [BAGraph.splitG, List.mem_map] at hΔ
  obtain ⟨r, hr, rfl⟩ := hΔ
  exact (BAVocab_split_props Γ.solid r hr).1 e he

/-- The edge counts of a term of `splitG`: the waved, dotted and `Ψ`-dotted edges are those of `Γ`, and
each solid edge of `Γ` becomes one solid or one `M`-dotted edge. -/
theorem BAGraph.splitG_edges {E I : Type} (Γ : BAGraph E I) :
    ∀ Δ ∈ Γ.splitG,
      Δ.nW = Γ.nW ∧ Δ.dotted = Γ.dotted ∧ Δ.psi = Γ.psi ∧
        Δ.nS + Δ.mdot.length = Γ.nS + Γ.mdot.length := by
  intro Δ hΔ
  simp only [BAGraph.splitG, List.mem_map] at hΔ
  obtain ⟨r, hr, rfl⟩ := hΔ
  refine ⟨rfl, rfl, rfl, ?_⟩
  have h := (BAVocab_split_props Γ.solid r hr).2
  simp only [BAGraph.nS, List.length_append]
  omega

end Split

/-! ## 7. Merging the `=`-dotted classes (`B:340`): the value of the merged graph -/

section Merge

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem BAVocab_vmap_eq_of_rel (Γ : RBM.Graph.LGraph E I) {u v : E ⊕ I} (h : Γ.EqRel u v) :
    Γ.vmap u = Γ.vmap v :=
  congrArg Γ.vmapC (Quotient.sound (Relation.EqvGen.rel _ _ h))

private theorem BAVocab_good_eq_of_cls {Γ : RBM.Graph.LGraph E I} {ℓ : E ⊕ I → ι} (h : Γ.Good ℓ)
    {u v : E ⊕ I} (huv : Γ.cls u = Γ.cls v) : ℓ u = ℓ v := by
  have h' : Relation.EqvGen Γ.EqRel u v := Quotient.exact huv
  clear huv
  induction h' with
  | rel _ _ hr => exact h _ _ hr
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem BAVocab_lterm_zero (Γ : RBM.Graph.LGraph E I) (D : RBM.Graph.LData ι)
    {ℓ : E ⊕ I → ι} (h : ¬ Γ.Good ℓ) : Γ.term D ℓ = 0 := by
  unfold RBM.Graph.LGraph.Good at h
  push Not at h
  obtain ⟨u, v, ⟨e, he, heq, hxy⟩, hne⟩ := h
  have hne' : ℓ e.x ≠ ℓ e.y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact fun h => hne h.symm
  have h0 : DEdge.val ℓ e = 0 := by simp [DEdge.val, heq, hne']
  have hprod : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)
  simp [RBM.Graph.LGraph.term, hprod]

private theorem BAVocab_term_zero (Γ : BAGraph E I) (D : BALData ι) {ℓ : E ⊕ I → ι}
    (h : ¬ Γ.toLGraph.Good ℓ) : Γ.term D ℓ = 0 := by
  simp [BAGraph.term, BAVocab_lterm_zero Γ.toLGraph D.toLData h]

private theorem BAVocab_prod_dotted_merge (Γ : RBM.Graph.LGraph E I)
    (ℓ' : Γ.ExtCls ⊕ Γ.IntCls → ι) :
    ∀ l : List (DEdge (E ⊕ I)), (∀ e ∈ l, e ∈ Γ.dotted) →
      ((l.filter fun e => !e.eq).map (DEdge.val (ℓ' ∘ Γ.vmap))).prod =
        (l.map (DEdge.val (ℓ' ∘ Γ.vmap))).prod
  | [], _ => rfl
  | e :: l, h => by
    have ih := BAVocab_prod_dotted_merge Γ ℓ' l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases heq : e.eq
    · simp [heq, ih]
    · have hv : Γ.vmap e.x = Γ.vmap e.y :=
        BAVocab_vmap_eq_of_rel Γ ⟨e, h e (List.mem_cons_self), heq, Or.inl ⟨rfl, rfl⟩⟩
      have h1 : DEdge.val (ℓ' ∘ Γ.vmap) e = 1 := by simp [DEdge.val, heq, hv]
      simp [heq, ih, h1]

private theorem BAVocab_lterm_merge (Γ : RBM.Graph.LGraph E I) (D : RBM.Graph.LData ι)
    (ℓ' : Γ.ExtCls ⊕ Γ.IntCls → ι) : Γ.merge.term D ℓ' = Γ.term D (ℓ' ∘ Γ.vmap) := by
  have hS : (SEdge.val D ℓ') ∘ (SEdge.map Γ.vmap) = SEdge.val D (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hW : (WEdge.val D ℓ') ∘ (WEdge.map Γ.vmap) = WEdge.val D (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hDm : (DEdge.val ℓ') ∘ (DEdge.map Γ.vmap) = DEdge.val (ℓ' ∘ Γ.vmap) := funext fun e => rfl
  have hD := BAVocab_prod_dotted_merge Γ ℓ' Γ.dotted fun e he => he
  simp only [RBM.Graph.LGraph.term, RBM.Graph.LGraph.merge, List.map_map, hS, hW, hDm]
  rw [hD]

/-- The product of the edge factors of the merged graph is that of `Γ` at the pulled-back labelling. -/
private theorem BAVocab_term_merge (Γ : BAGraph E I) (D : BALData ι)
    (ℓ' : Γ.toLGraph.ExtCls ⊕ Γ.toLGraph.IntCls → ι) :
    Γ.merge.term D ℓ' = Γ.term D (ℓ' ∘ Γ.toLGraph.vmap) := by
  have hL := BAVocab_lterm_merge Γ.toLGraph D.toLData ℓ'
  have hP : ((Γ.psi.map (BAPsiEdge.map Γ.toLGraph.vmap)).map (BAPsiEdge.val D ℓ')) =
      Γ.psi.map (BAPsiEdge.val D (ℓ' ∘ Γ.toLGraph.vmap)) := by
    rw [List.map_map]; rfl
  have hM : ((Γ.mdot.map (BAMEdge.map Γ.toLGraph.vmap)).map (BAMEdge.val D ℓ')) =
      Γ.mdot.map (BAMEdge.val D (ℓ' ∘ Γ.toLGraph.vmap)) := by
    rw [List.map_map]; rfl
  simp only [BAGraph.term, BAGraph.merge, hP, hM]
  rw [hL]

private theorem BAVocab_vmap_inl (Γ : RBM.Graph.LGraph E I) (a : E) :
    Γ.vmap (Sum.inl a) = Sum.inl (Γ.extMap a) := by
  have h : Γ.IsExtCls (Γ.cls (Sum.inl a)) := ⟨a, rfl⟩
  simp [RBM.Graph.LGraph.vmap, RBM.Graph.LGraph.vmapC, RBM.Graph.LGraph.extMap, h]

private theorem BAVocab_vmap_inr_ext (Γ : RBM.Graph.LGraph E I) (b : I)
    (h : Γ.IsExtCls (Γ.cls (Sum.inr b))) :
    Γ.vmap (Sum.inr b) = Sum.inl ⟨Γ.cls (Sum.inr b), h⟩ := by
  simp [RBM.Graph.LGraph.vmap, RBM.Graph.LGraph.vmapC, h]

private theorem BAVocab_vmap_inr_int (Γ : RBM.Graph.LGraph E I) (b : I)
    (h : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b))) :
    Γ.vmap (Sum.inr b) = Sum.inr ⟨Γ.cls (Sum.inr b), h⟩ := by
  simp [RBM.Graph.LGraph.vmap, RBM.Graph.LGraph.vmapC, h]

private theorem BAVocab_exists_inr_of_int (Γ : RBM.Graph.LGraph E I) (q : Γ.IntCls) :
    ∃ b : I, Γ.cls (Sum.inr b) = q.1 := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep q.1
  rcases v with a | b
  · exact absurd ⟨a, hv⟩ q.2
  · exact ⟨b, hv⟩

/-- Merging preserves the value, for the external labels that factor through the merge. -/
private theorem BAVocab_val_eq_merge_val (Γ : BAGraph E I) (D : BALData ι)
    (ℓ' : Γ.toLGraph.ExtCls → ι) :
    Γ.val D (ℓ' ∘ Γ.toLGraph.extMap) = Γ.merge.val D ℓ' := by
  classical
  set Φ : (Γ.toLGraph.IntCls → ι) → (I → ι) :=
    fun ℓi' b => (Sum.elim ℓ' ℓi') (Γ.toLGraph.vmap (Sum.inr b)) with hΦ
  have hlab : ∀ ℓi', Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) (Φ ℓi') =
      (Sum.elim ℓ' ℓi') ∘ Γ.toLGraph.vmap := by
    intro ℓi'
    funext v
    rcases v with a | b
    · simp [BAVocab_vmap_inl]
    · rfl
  have hRHS : Γ.merge.val D ℓ' =
      ∑ ℓi', Γ.term D (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) (Φ ℓi')) := by
    unfold BAGraph.val
    refine Finset.sum_congr rfl fun ℓi' _ => ?_
    rw [BAVocab_term_merge, hlab]
  have hinj : Function.Injective Φ := by
    intro f g hfg
    funext q
    obtain ⟨b, hb⟩ := BAVocab_exists_inr_of_int Γ.toLGraph q
    have hq : ¬ Γ.toLGraph.IsExtCls (Γ.toLGraph.cls (Sum.inr b)) := by rw [hb]; exact q.2
    have hv : Γ.toLGraph.vmap (Sum.inr b) = Sum.inr q := by
      rw [BAVocab_vmap_inr_int Γ.toLGraph b hq]
      congr 1
      exact Subtype.ext hb
    have := congrFun hfg b
    simpa [hΦ, hv] using this
  have hrange : ∀ ℓi : I → ι, ℓi ∉ Set.range Φ →
      Γ.term D (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) ℓi) = 0 := by
    intro ℓi hℓi
    apply BAVocab_term_zero
    intro hgood
    apply hℓi
    refine ⟨fun q => ℓi (Classical.choose (BAVocab_exists_inr_of_int Γ.toLGraph q)), ?_⟩
    funext b
    by_cases hext : Γ.toLGraph.IsExtCls (Γ.toLGraph.cls (Sum.inr b))
    · obtain ⟨a, ha⟩ := hext
      have h1 := BAVocab_good_eq_of_cls hgood (u := Sum.inl a) (v := Sum.inr b) ha
      simp only [hΦ, BAVocab_vmap_inr_ext Γ.toLGraph b ⟨a, ha⟩, Sum.elim_inl, Sum.elim_inr,
        Function.comp_apply] at h1 ⊢
      rw [← h1]
      congr 1
      exact Subtype.ext ha.symm
    · have hc := Classical.choose_spec
        (BAVocab_exists_inr_of_int Γ.toLGraph ⟨Γ.toLGraph.cls (Sum.inr b), hext⟩)
      have h1 := BAVocab_good_eq_of_cls hgood
        (u := Sum.inr (Classical.choose
          (BAVocab_exists_inr_of_int Γ.toLGraph ⟨Γ.toLGraph.cls (Sum.inr b), hext⟩)))
        (v := Sum.inr b) hc
      simp only [hΦ, BAVocab_vmap_inr_int Γ.toLGraph b hext, Sum.elim_inr]
      simpa using h1
  rw [hRHS]
  unfold BAGraph.val
  rw [← Finset.sum_image (f := fun ℓi => Γ.term D (Sum.elim (ℓ' ∘ Γ.toLGraph.extMap) ℓi))
    (fun x _ y _ h => hinj h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro ℓi _ hni
  apply hrange
  rintro ⟨x, hx⟩
  exact hni (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩)

private theorem BAVocab_val_of_factor {E : Type} (P : BAPGraph E) (D : BALData ι) {ℓe : E → ι}
    {ℓ' : P.E' → ι} (h : ℓe = ℓ' ∘ P.ext) : P.val D ℓe = P.g.val D ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [BAPGraph.val, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

private theorem BAVocab_val_of_not {E : Type} (P : BAPGraph E) (D : BALData ι) {ℓe : E → ι}
    (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : P.val D ℓe = 0 := by
  classical
  simp only [BAPGraph.val, h, ↓reduceDIte]

/-- The merged graph has the value of the graph, for all external labels (including those that give
different labels to merged external vertices: both values are `0`). -/
private theorem BAVocab_packMerge_val (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) :
    Γ.packMerge.val D ℓe = Γ.val D ℓe := by
  classical
  by_cases h : ∃ ℓ' : Γ.toLGraph.ExtCls → ι, ℓe = ℓ' ∘ Γ.toLGraph.extMap
  · obtain ⟨ℓ', hℓ⟩ := h
    rw [BAVocab_val_of_factor Γ.packMerge D hℓ]
    subst hℓ
    exact (BAVocab_val_eq_merge_val Γ D ℓ').symm
  · rw [BAVocab_val_of_not Γ.packMerge D h]
    unfold BAGraph.val
    refine (Finset.sum_eq_zero fun ℓi _ => BAVocab_term_zero Γ D ?_).symm
    intro hgood
    apply h
    refine ⟨fun q => ℓe (Classical.choose q.2), ?_⟩
    funext a
    have hc := Classical.choose_spec (Γ.toLGraph.extMap a).2
    have := BAVocab_good_eq_of_cls hgood
      (u := Sum.inl (Classical.choose (Γ.toLGraph.extMap a).2)) (v := Sum.inl a) hc
    simpa using this.symm

end Merge

/-! ## 8. The partition (`B:339-341`) -/

section Partition

/-- **The partition preserves the value** (`B:339-341`): `G = Ǧ + M` on every solid edge, then the
`=`-dotted classes are merged.  No hypothesis on the data `D` is needed (unlike
`LGraph.val_eq_partition`, which needs `M = m I` on the diagonal). -/
theorem BAGraph.val_eq_partition {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : BAGraph E I) (D : BALData ι) (ℓe : E → ι) :
    Γ.val D ℓe = BAComb.val Γ.partition D ℓe := by
  unfold BAComb.val BAGraph.partition
  rw [List.map_map]
  have h : ∀ Δ ∈ Γ.splitG, ((fun P : BAPGraph E => P.val D ℓe) ∘ BAGraph.packMerge) Δ =
      Δ.val D ℓe := fun Δ _ => BAVocab_packMerge_val Δ D ℓe
  rw [List.map_congr_left h, BAGraph.val_splitG]

/-- **The terms of the partition are normal graphs** (`defn_normalBA`, `B:331-343`). -/
theorem BAGraph.partition_normal {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : BAGraph E I) : ∀ P ∈ Γ.partition, P.g.Normal := by
  intro P hP
  simp only [BAGraph.partition, List.mem_map] at hP
  obtain ⟨Δ, hΔ, rfl⟩ := hP
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    obtain ⟨_, hq⟩ := List.mem_filter.1 he0
    simpa [DEdge.map] using hq
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact BAGraph.splitG_circ Γ Δ hΔ e0 he0

end Partition

/-! ## 9. The partition of a normal graph is the graph (`B:331-343`, `B:354-355`) -/

section Equiv

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

private theorem BAVocab_step_equiv (r : α → α → Bool) (r' : β → β → Bool) (φ : α ≃ β)
    (hr : ∀ u v, r' (φ u) (φ v) = r u v) (s : Finset α) :
    BAVocab_step r' (s.map φ.toEmbedding) = (BAVocab_step r s).map φ.toEmbedding := by
  ext w'
  obtain ⟨w, rfl⟩ := φ.surjective w'
  simp only [BAVocab_step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Equiv.symm_apply_apply]
  constructor
  · rintro (h | ⟨v', hv', hadj⟩)
    · exact Or.inl h
    · refine Or.inr ⟨φ.symm v', hv', ?_⟩
      rw [← hr, Equiv.apply_symm_apply]
      exact hadj
  · rintro (h | ⟨v, hv, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨φ v, by simpa using hv, by rw [hr]; exact hadj⟩

private theorem BAVocab_iterate_equiv (r : α → α → Bool) (r' : β → β → Bool) (φ : α ≃ β)
    (hr : ∀ u v, r' (φ u) (φ v) = r u v) (n : ℕ) :
    ∀ s : Finset α, (BAVocab_step r')^[n] (s.map φ.toEmbedding) =
      ((BAVocab_step r)^[n] s).map φ.toEmbedding := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, BAVocab_step_equiv r r' φ hr, ih]

private theorem BAVocab_closure_equiv (r : α → α → Bool) (r' : β → β → Bool) (φ : α ≃ β)
    (hr : ∀ u v, r' (φ u) (φ v) = r u v) (v : α) :
    (BAVocab_step r')^[Fintype.card β] {φ v} =
      ((BAVocab_step r)^[Fintype.card α] {v}).map φ.toEmbedding := by
  have h1 : ({φ v} : Finset β) = ({v} : Finset α).map φ.toEmbedding := by simp
  rw [show Fintype.card β = Fintype.card α from (Fintype.card_congr φ).symm, h1,
    BAVocab_iterate_equiv r r' φ hr]

end Equiv

section NormalAgree

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAVocab_cnt_equiv {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I']
    [DecidableEq I'] (φ : E ⊕ I ≃ E' ⊕ I') (hφ : ∀ v, (φ v).isRight = v.isRight)
    (cl : E ⊕ I → Finset (E ⊕ I)) (cl' : E' ⊕ I' → Finset (E' ⊕ I'))
    (hcl : ∀ v, cl' (φ v) = (cl v).map φ.toEmbedding) :
    ((Finset.univ.filter fun v' : E' ⊕ I' => ∀ w ∈ cl' v', w.isRight = true).image cl').card =
      ((Finset.univ.filter fun v : E ⊕ I => ∀ w ∈ cl v, w.isRight = true).image cl).card := by
  have hP : ∀ v, (∀ w ∈ cl' (φ v), w.isRight = true) ↔ ∀ w ∈ cl v, w.isRight = true := by
    intro v
    rw [hcl]
    constructor
    · intro h w hw
      have := h (φ w) (Finset.mem_map_of_mem _ hw)
      rwa [hφ] at this
    · intro h w' hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hw'
      rw [Equiv.coe_toEmbedding, hφ]
      exact h w hw
  have himg : (Finset.univ.filter fun v' : E' ⊕ I' => ∀ w ∈ cl' v', w.isRight = true).image cl' =
      ((Finset.univ.filter fun v : E ⊕ I => ∀ w ∈ cl v, w.isRight = true).image cl).image
        (Finset.map φ.toEmbedding) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v', hv', rfl⟩
      obtain ⟨v, rfl⟩ := φ.surjective v'
      exact ⟨cl v, ⟨v, (hP v).1 hv', rfl⟩, (hcl v).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨φ v, (hP v).2 hv, hcl v⟩
  rw [himg, Finset.card_image_of_injective _ (Finset.map_injective _)]

private theorem BAVocab_cls_eq_iff (Γ : RBM.Graph.LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false)
    (u v : E ⊕ I) : Γ.cls u = Γ.cls v ↔ u = v := by
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

private theorem BAVocab_vmapC_injective (Γ : RBM.Graph.LGraph E I) : Function.Injective Γ.vmapC := by
  intro q q' h
  unfold RBM.Graph.LGraph.vmapC at h
  by_cases hq : Γ.IsExtCls q <;> by_cases hq' : Γ.IsExtCls q' <;> simp [hq, hq'] at h
  · exact h
  · exact h

private theorem BAVocab_vmap_injective (Γ : RBM.Graph.LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    Function.Injective Γ.vmap := by
  intro u v huv
  exact (BAVocab_cls_eq_iff Γ h u v).1 (BAVocab_vmapC_injective Γ huv)

private theorem BAVocab_vmap_surjective (Γ : RBM.Graph.LGraph E I) : Function.Surjective Γ.vmap := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [RBM.Graph.LGraph.vmap, RBM.Graph.LGraph.vmapC, hq]⟩
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨v, by simp [RBM.Graph.LGraph.vmap, RBM.Graph.LGraph.vmapC, hq]⟩

private theorem BAVocab_vmap_isRight (Γ : RBM.Graph.LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false)
    (v : E ⊕ I) : (Γ.vmap v).isRight = v.isRight := by
  rcases v with a | b
  · rw [BAVocab_vmap_inl]; rfl
  · have hq : ¬ Γ.IsExtCls (Γ.cls (Sum.inr b)) := by
      rintro ⟨a, ha⟩
      exact absurd ((BAVocab_cls_eq_iff Γ h _ _).1 ha) (by simp)
    rw [BAVocab_vmap_inr_int Γ b hq]
    rfl

private theorem BAVocab_dotted_any_false {V : Type*} (l : List (DEdge V))
    (h : ∀ e ∈ l, e.eq = false) (p : DEdge V → Bool) : l.any (fun e => e.eq && p e) = false := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp [List.any_cons, h e List.mem_cons_self, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]

private theorem BAVocab_merge_dotted_eq (Γ : BAGraph E I) :
    ∀ e ∈ Γ.merge.dotted, e.eq = false := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨_, hq⟩ := List.mem_filter.1 he0
  simpa [DEdge.map] using hq

private theorem BAVocab_merge_atomAdj (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false)
    (u v : E ⊕ I) :
    Γ.merge.atomAdj (Γ.toLGraph.vmap u) (Γ.toLGraph.vmap v) = Γ.atomAdj u v := by
  have hinj := BAVocab_vmap_injective Γ.toLGraph h
  unfold BAGraph.atomAdj
  rw [BAVocab_dotted_any_false _ (BAVocab_merge_dotted_eq Γ), BAVocab_dotted_any_false _ h]
  simp only [BAGraph.merge, List.any_map, Function.comp_def, BAPsiEdge.map, BAMEdge.map,
    hinj.eq_iff]

private theorem BAVocab_merge_adj (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false)
    (u v : E ⊕ I) :
    Γ.merge.adj (Γ.toLGraph.vmap u) (Γ.toLGraph.vmap v) = Γ.adj u v := by
  have hinj := BAVocab_vmap_injective Γ.toLGraph h
  have hat := BAVocab_merge_atomAdj Γ h u v
  unfold BAGraph.adj
  rw [hat]
  congr 1
  unfold RBM.Graph.LGraph.adj
  rw [BAVocab_dotted_any_false _ (BAVocab_merge_dotted_eq Γ), BAVocab_dotted_any_false _ h]
  simp only [BAGraph.merge, RBM.Graph.LGraph.merge, List.any_map, Function.comp_def,
    WEdge.map, hinj.eq_iff]

/-- Without `=`-dotted edges the merge is a relabeling by a bijection that keeps external and internal
vertices apart, and the counters are unchanged. -/
private theorem BAVocab_merge_counters (Γ : BAGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    Γ.merge.counters = Γ.counters := by
  have hinj := BAVocab_vmap_injective Γ.toLGraph h
  set φ : E ⊕ I ≃ Γ.toLGraph.ExtCls ⊕ Γ.toLGraph.IntCls :=
    Equiv.ofBijective Γ.toLGraph.vmap ⟨hinj, BAVocab_vmap_surjective Γ.toLGraph⟩ with hφ
  have hφR : ∀ v, (φ v).isRight = v.isRight := BAVocab_vmap_isRight Γ.toLGraph h
  have hnS : Γ.merge.nS = Γ.nS := by simp [BAGraph.nS, BAGraph.merge, RBM.Graph.LGraph.merge]
  have hnW : Γ.merge.nW = Γ.nW := by simp [BAGraph.nW, BAGraph.merge, RBM.Graph.LGraph.merge]
  have hnA : Γ.merge.nA = Γ.nA := by
    unfold BAGraph.nA
    refine BAVocab_cnt_equiv φ hφR Γ.atom Γ.merge.atom fun v => ?_
    exact BAVocab_closure_equiv (fun a b => Γ.atomAdj a b) (fun a b => Γ.merge.atomAdj a b) φ
      (fun u w => BAVocab_merge_atomAdj Γ h u w) v
  have hnM : Γ.merge.nM = Γ.nM := by
    unfold BAGraph.nM
    refine BAVocab_cnt_equiv φ hφR Γ.mol Γ.merge.mol fun v => ?_
    exact BAVocab_closure_equiv (fun a b => Γ.adj a b) (fun a b => Γ.merge.adj a b) φ
      (fun u w => BAVocab_merge_adj Γ h u w) v
  unfold BAGraph.counters
  rw [hnS, hnW, hnA, hnM]

private theorem BAVocab_baSplitSolid_circ {V : Type*} :
    ∀ es : List (SEdge V), (∀ e ∈ es, e.circ = true) → baSplitSolid es = [(es, [])]
  | [], _ => rfl
  | e :: es, h => by
    have ih := BAVocab_baSplitSolid_circ es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    simp [baSplitSolid, ih, h e List.mem_cons_self]

/-- **The partition of a normal graph is the graph** (`B:331-343`): one term, the merge of `Γ` (a
relabeling, since `Γ` has no `=`-dotted edge), with the counters of `Γ`. -/
theorem BAGraph.partition_of_normal {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : BAGraph E I) :
    Γ.Normal → ∃ P : BAPGraph E, Γ.partition = [P] ∧ P.counters = Γ.counters := by
  intro hN
  have hsplit : Γ.splitG = [Γ] := by
    unfold BAGraph.splitG
    rw [BAVocab_baSplitSolid_circ Γ.solid hN.2]
    obtain ⟨⟨s, w, d, c⟩, p, m⟩ := Γ
    rfl
  refine ⟨Γ.packMerge, ?_, ?_⟩
  · unfold BAGraph.partition
    rw [hsplit]
    rfl
  · exact BAVocab_merge_counters Γ hN.1

/-- `k ≤ ord(Γ)` for a general graph iff `k ≤ ord(P)` for every graph `P` of the partition
(the minimum of `B:354-355`). -/
theorem BAGraph.le_scalingOrderG_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : BAGraph E I) (k : ℤ) :
    ((k : ℤ) : WithTop ℤ) ≤ Γ.scalingOrderG ↔ ∀ P ∈ Γ.partition, k ≤ P.scalingOrder := by
  unfold BAGraph.scalingOrderG
  generalize Γ.partition = L
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.map_cons, List.foldr_cons, le_min_iff, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    simp [WithTop.coe_le_coe]

/-- On a normal graph the scaling order of a general graph is the scaling order. -/
theorem BAGraph.scalingOrderG_of_normal {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]
    [DecidableEq I] (Γ : BAGraph E I) :
    Γ.Normal → Γ.scalingOrderG = ((Γ.scalingOrder : ℤ) : WithTop ℤ) := by
  intro hN
  obtain ⟨P, hP, hc⟩ := Γ.partition_of_normal hN
  simp [BAGraph.scalingOrderG, hP, BAGraph.scalingOrder, BAPGraph.scalingOrder, hc]

end NormalAgree

/-! ## 10. Compiled instances (the instances of the ticket and one application of every theorem) -/

namespace BAVocabInst

/-- `Ǧ_{y'x} Ǧ_{xy}`, the left side of `GGGamma` (`B:395`): `y', y = inl 0, inl 1`, `x = inr 0`. -/
def baGGLhs : BAGraph (Fin 2) (Fin 1) where
  solid := [⟨true, true, .inl 0, .inr 0⟩, ⟨true, true, .inr 0, .inl 1⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- The first sum of `GGGamma` with the D402 coefficient, one term: `M_{xu} M_{ux} S⁺_{uβ} M_{βy} M_{y'β}`
(`x, u, β = inr 0, inr 1, inr 2`). -/
def baGGT1 : BAGraph (Fin 2) (Fin 3) where
  solid := []
  waved := [⟨true, true, .inr 1, .inr 2⟩]
  dotted := []
  coeff := 1
  psi := []
  mdot := [⟨true, .inr 0, .inr 1⟩, ⟨true, .inr 1, .inr 0⟩, ⟨true, .inr 2, .inl 1⟩, ⟨true, .inl 0, .inr 2⟩]

/-- The `δ_{xy}` part of the first term of `lem_lweight` (`B:380`): `M_{xα} S_{αβ} Ǧ_{αx} Ǧ_{ββ}`
(`x, α, β = inr 0, inr 1, inr 2`). -/
def baLWT1 : BAGraph (Fin 0) (Fin 3) where
  solid := [⟨true, true, .inr 1, .inr 0⟩, ⟨true, true, .inr 2, .inr 2⟩]
  waved := [⟨false, true, .inr 1, .inr 2⟩]
  dotted := []
  coeff := 1
  psi := []
  mdot := [⟨true, .inr 0, .inr 1⟩]

/-- One `G` edge `G_{ax}` (`a = inl 0`, `x = inr 0`): its partition has two terms, `Ǧ_{ax}` and `M_{ax}`. -/
def baGedge : BAGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- A graph with a `=`-dotted edge between the external `a = inl 0` and the internal `x = inr 0`, a `G`
edge `G_{ax}`, a weight `G_{xx}` and a `Ψ`-dotted edge `x — a`. -/
def baEqGraph : BAGraph (Fin 1) (Fin 1) where
  solid := [⟨true, false, .inl 0, .inr 0⟩, ⟨true, false, .inr 0, .inr 0⟩]
  waved := []
  dotted := [⟨true, .inl 0, .inr 0⟩]
  coeff := 1
  psi := [⟨.inr 0, .inl 0⟩]
  mdot := []

/-- Data on the labels `Fin 2` (integer entries, nondegenerate: `M` is not a multiple of the identity). -/
def baD : BALData (Fin 2) where
  G := Matrix.of ![![1, 2], ![3, 4]]
  M := Matrix.of ![![5, 6], ![7, 8]]
  S := Matrix.of ![![1, 1], ![1, 2]]
  Sp := Matrix.of ![![0, 1], ![1, 0]]
  gPsi := Matrix.of ![![2, 1], ![1, 3]]

-- (I1)
theorem baGGLhs_counters : baGGLhs.counters = ⟨2, 0, 1, 1, 0, 0⟩ := by
  have h : baGGLhs.nS = 2 ∧ baGGLhs.nW = 0 ∧ baGGLhs.nA = 1 ∧ baGGLhs.nM = 1 := by decide
  simp only [BAGraph.counters, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem baGGLhs_ord : baGGLhs.scalingOrder = 0 := by
  simp [BAGraph.scalingOrder, baGGLhs_counters, ord]

-- (I2) (D402 coefficient)
theorem baGGT1_counters : baGGT1.counters = ⟨0, 1, 1, 0, 0, 0⟩ := by
  have h : baGGT1.nS = 0 ∧ baGGT1.nW = 1 ∧ baGGT1.nA = 1 ∧ baGGT1.nM = 0 := by decide
  simp only [BAGraph.counters, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem baGGT1_ord : baGGT1.scalingOrder = 0 := by
  simp [BAGraph.scalingOrder, baGGT1_counters, ord]

-- (I3)
theorem baLWT1_counters : baLWT1.counters = ⟨2, 1, 2, 1, 0, 0⟩ := by
  have h : baLWT1.nS = 2 ∧ baLWT1.nW = 1 ∧ baLWT1.nA = 2 ∧ baLWT1.nM = 1 := by decide
  simp only [BAGraph.counters, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem baLWT1_ord : baLWT1.scalingOrder = 0 := by
  simp [BAGraph.scalingOrder, baLWT1_counters, ord]

-- (I4)
theorem baGedge_ord : baGedge.scalingOrder = -1 := by
  have h : baGedge.nS = 1 ∧ baGedge.nW = 0 ∧ baGedge.nA = 1 ∧ baGedge.nM = 1 := by decide
  simp [BAGraph.scalingOrder, BAGraph.counters, ord, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem baGedge_splitG_length : baGedge.splitG.length = 2 := by decide

theorem baGedge_not_normal : ¬ baGedge.Normal := by
  intro h
  have := h.2 ⟨true, false, .inl 0, .inr 0⟩ (by simp [baGedge])
  simp at this

theorem baGedge_splitG_circ : ∀ Δ ∈ baGedge.splitG, ∀ e ∈ Δ.solid, e.circ = true :=
  BAGraph.splitG_circ baGedge

-- (I5)
theorem p2Graph_ba_ord : (BAGraph.ofLGraph p2Graph).scalingOrder = 2 := by
  rw [BAGraph.scalingOrder_ofLGraph p2Graph (by decide)]
  exact p2Graph_ord

theorem figGraph_ba_ord : (BAGraph.ofLGraph figGraph).scalingOrder = 4 := by
  rw [BAGraph.scalingOrder_ofLGraph figGraph (by decide)]
  exact figGraph_ord

/-- The terms of `splitG` of `baGedge`: `Ǧ_{ax}` and `M_{ax}`. -/
def baGedge1 : BAGraph (Fin 1) (Fin 1) where
  solid := [⟨true, true, .inl 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

def baGedge2 : BAGraph (Fin 1) (Fin 1) where
  solid := []
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := [⟨true, .inl 0, .inr 0⟩]

theorem baGedge_splitG : baGedge.splitG = [baGedge1, baGedge2] := rfl

theorem baGedge1_normal : baGedge1.Normal := ⟨by decide, by decide⟩

theorem baGedge2_normal : baGedge2.Normal := ⟨by decide, by decide⟩

-- (I6), order: `ord(Ǧ_{ax}) = -1`, `ord(M_{ax}) = 0`, hence `ord(G_{ax}) = -1`.
theorem baGedge_ordG : baGedge.scalingOrderG = (((-1 : ℤ)) : WithTop ℤ) := by
  have h1 : baGedge1.nS = 1 ∧ baGedge1.nW = 0 ∧ baGedge1.nA = 1 ∧ baGedge1.nM = 1 := by decide
  have h2 : baGedge2.nS = 0 ∧ baGedge2.nW = 0 ∧ baGedge2.nA = 0 ∧ baGedge2.nM = 0 := by decide
  have e1 : (BAGraph.packMerge baGedge1).scalingOrder = -1 := by
    unfold BAPGraph.scalingOrder
    have : (BAGraph.packMerge baGedge1).counters = baGedge1.counters :=
      BAVocab_merge_counters baGedge1 (by decide)
    rw [this]
    simp [BAGraph.counters, ord, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  have e2 : (BAGraph.packMerge baGedge2).scalingOrder = 0 := by
    unfold BAPGraph.scalingOrder
    have : (BAGraph.packMerge baGedge2).counters = baGedge2.counters :=
      BAVocab_merge_counters baGedge2 (by decide)
    rw [this]
    simp [BAGraph.counters, ord, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]
  unfold BAGraph.scalingOrderG BAGraph.partition
  rw [baGedge_splitG]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e1, e2, min_top_right]
  exact min_eq_left (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))

/-- The sum over the labels of one internal vertex. -/
private theorem BAVocab_val_fin_one {ι E : Type} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E (Fin 1))
    (D : BALData ι) (ℓe : E → ι) : Γ.val D ℓe = ∑ x : ι, Γ.term D (Sum.elim ℓe fun _ => x) := by
  unfold BAGraph.val
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ (fun f => ?_)
  congr 2
  funext i
  rw [Subsingleton.elim i default]
  rfl

-- (I6), value: at the data `baD`, `ℓ_a = 0`: `G_{ax}` sums to `G_{00} + G_{01} = 3`, `Ǧ_{ax}` to `-8`,
-- `M_{ax}` to `11`.
theorem baGedge_val : baGedge.val baD (fun _ => 0) = 3 := by
  rw [BAVocab_val_fin_one]
  simp [BAGraph.term, RBM.Graph.LGraph.term, baGedge, SEdge.val, baD, Fin.sum_univ_two]
  norm_num

theorem baGedge1_val : baGedge1.val baD (fun _ => 0) = -8 := by
  rw [BAVocab_val_fin_one]
  simp [BAGraph.term, RBM.Graph.LGraph.term, baGedge1, SEdge.val, baD, Fin.sum_univ_two]
  norm_num

theorem baGedge2_val : baGedge2.val baD (fun _ => 0) = 11 := by
  rw [BAVocab_val_fin_one]
  simp [BAGraph.term, RBM.Graph.LGraph.term, baGedge2, BAMEdge.val, baD, Fin.sum_univ_two]
  norm_num

/-- The scaling size of `baGGLhs` at `Ψ = 1/2`, `W = 4`, `d = 3`, `L = 8`:
`(8^3)^1 (1/2)^2 4^{3} = 8192` (`n_M = 1`, `n_S = 2`, `n_W - n_A = -1`). -/
theorem baGGLhs_size : baGGLhs.scalingSize (1 / 2) 4 3 8 = 8192 := by
  unfold BAGraph.scalingSize
  rw [baGGLhs_counters]
  simp only [Counters.scalingSize]
  norm_num

/-- The value identity `Γ.val = BAComb.val Γ.partition` at the data `baD`, `ℓ_a = 0`, evaluated:
the terms `Ǧ_{ax}` and `M_{ax}` of `G_{ax}` give `-8 + 11 = 3`. -/
theorem baGedge_split_sum : (baGedge.splitG.map fun Δ => Δ.val baD (fun _ => 0)).sum = 3 := by
  rw [baGedge_splitG]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, baGedge1_val, baGedge2_val]
  norm_num

theorem baGedge_partition_val : BAComb.val baGedge.partition baD (fun _ => 0) = 3 := by
  rw [← BAGraph.val_eq_partition, baGedge_val]

/-! One application of every public theorem at concrete data (all deterministic hypotheses
discharged; `ι = Fin 2`, the graphs above). -/

example := BAGraph.val_ofLGraph p2Graph baD ![0, 1]

example := BAGraph.term_addM baGedge ⟨true, .inl 0, .inr 0⟩ baD (fun _ => 0)

/-- `inr 2` lies in the atom of `inl 0` (joined by the `M`-dotted edge `M_{y'β}`). -/
example : (Sum.inr 2 : Fin 2 ⊕ Fin 3) ∈ baGGT1.atom (.inl 0) :=
  (BAGraph.mem_atom_iff _ _ _).2 (Relation.ReflTransGen.single (by decide))

/-- `inr 1` lies in the molecule of `inl 0` (an `M`-dotted edge, then the waved edge `S⁺_{uβ}`) but not
in its atom. -/
example : (Sum.inr 1 : Fin 2 ⊕ Fin 3) ∈ baGGT1.mol (.inl 0) :=
  (BAGraph.mem_mol_iff _ _ _).2 (Relation.ReflTransGen.tail (b := (Sum.inr 2 : Fin 2 ⊕ Fin 3))
    (Relation.ReflTransGen.single (by decide)) (by decide))

example : (Sum.inr 1 : Fin 2 ⊕ Fin 3) ∉ baGGT1.atom (.inl 0) := by decide

example := BAGraph.atom_subset_mol baGGT1 (.inl 0)

example : baGGT1.nA ≤ Fintype.card (Fin 3) := BAGraph.nA_le_card baGGT1

example : baGGT1.nM ≤ baGGT1.nA := BAGraph.nM_le_nA baGGT1

example := BAGraph.counters_ofLGraph p2Graph (by decide)

example := BAGraph.scalingOrder_ofLGraph figGraph (by decide)

example := BAGraph.scalingSize_eq baGGLhs (Ψ := 1 / 2) 4 3 8 (by norm_num)

example := BAGraph.val_splitG baGedge baD (fun _ => 0)

example := BAGraph.splitG_circ baGedge

example := BAGraph.splitG_edges baGedge

example := BAGraph.val_eq_partition baGedge baD (fun _ => 0)

/-- A graph with a `=`-dotted edge, a `Ψ`-dotted edge and a weight: the partition merges `a` and `x`. -/
example := BAGraph.val_eq_partition baEqGraph baD (fun _ => 0)

example := BAGraph.partition_normal baEqGraph

example := BAGraph.partition_of_normal baGGLhs ⟨by decide, by decide⟩

example := BAGraph.le_scalingOrderG_iff baGedge (-1)

example := BAGraph.scalingOrderG_of_normal baGGT1 ⟨by decide, by decide⟩

end BAVocabInst
end RBM.Graph
