/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.LocalRegular2

/-!
# BA-L R0, part 2: the band lift and the path pin `BAPathLift` (T2417)

Second file of the row R0 (`RBM3D/Graph/BAAtomic.lean` is the first): the BA-normal lift `liftC` of
a packed band graph (every solid edge circled, no `Ψ`- or `M`-dotted edge; T2397 probe 219-246) and
the map property `BAPathLift` (T2397 probe 355): at the lift of a normal band graph the coloured
path invariant `PGraph.PathInv2` (`LocalRegular2.lean:1577`) of the atomic image is that of the
graph.  It is `LGraph.localReg2_pathFam_map` (`LocalRegular2.lean:616`) along `vmap`, in both
directions: without `=`-dotted edges every atom is a vertex, so `vmap` is a bijection.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Graph

/-! ## 1. The band lift (T2397 probe 219-246; statements copied) -/

/-! ## 2. Without `=`-dotted edges every atom is a vertex -/

section OfL

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Without `=`-dotted edges every atom is a vertex (`BAVocab.lean`, private `BAVocab_atom_ofL`; copied from T2397 probe 195). -/
theorem BAAtomic_atom_ofL (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (v : E ⊕ I) :
    (BAGraph.ofLGraph Γ).atom v = {v} := by
  have hadj : ∀ u w, (BAGraph.ofLGraph Γ).atomAdj u w = false := by
    intro u w
    simp only [BAGraph.atomAdj, BAGraph.ofLGraph, List.any_nil, Bool.or_false]
    rw [Bool.eq_false_iff]
    intro hh
    simp only [List.any_eq_true, Bool.and_eq_true] at hh
    obtain ⟨e, he, he1, _⟩ := hh
    rw [h e he] at he1
    exact absurd he1 (by simp)
  ext w
  rw [BAGraph.mem_atom_iff, Finset.mem_singleton]
  refine ⟨fun hw => ?_, fun hw => hw ▸ Relation.ReflTransGen.refl⟩
  induction hw with
  | refl => rfl
  | tail _ hbc _ => exact absurd (hadj _ _ ▸ hbc) (by simp)

/-- At a graph without `=`-dotted edges, `vmap` is injective. -/
theorem BAAtomic_vmap_injective_ofL (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    Function.Injective (promoteC (BAGraph.ofLGraph Γ)).vmap := by
  intro u v huv
  have h1 := (BAAtomic_promoteC_vmap_eq_atom _ u v).1 huv
  rw [BAAtomic_atom_ofL Γ h, Finset.mem_singleton] at h1
  exact h1.symm

/-- The vertices of the merge of the BA reading of `Γ` are those of `Γ`. -/
def BAAtomic_vmapEquiv (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    E ⊕ I ≃ (promoteC (BAGraph.ofLGraph Γ)).ExtCls ⊕ (promoteC (BAGraph.ofLGraph Γ)).IntCls :=
  Equiv.ofBijective _ ⟨BAAtomic_vmap_injective_ofL Γ h, BAAtomic_vmap_surjective _⟩

theorem BAAtomic_reach_of_adj {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I')
    {a b : E' ⊕ I'} (h : Γ.adj a b = true) : Γ.molGraph.Reachable a b := by
  by_cases hab : a = b
  · subst hab; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩)

theorem BAAtomic_adj_of_waved {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I')
    {e0 : WEdge (E' ⊕ I')} (he0 : e0 ∈ Γ.waved) : Γ.adj e0.x e0.y = true := by
  unfold LGraph.adj
  simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact Or.inl ⟨e0, he0, Or.inl ⟨rfl, rfl⟩⟩

/-- Without `=`-dotted edges, the adjacency of the molecules is a waved edge. -/
theorem BAAtomic_adj_waved_of_noeq {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : LGraph E' I')
    (h : ∀ e ∈ Γ.dotted, e.eq = false) {a b : E' ⊕ I'} (hab : Γ.adj a b = true) :
    ∃ e0 ∈ Γ.waved, ((e0.x = a ∧ e0.y = b) ∨ (e0.x = b ∧ e0.y = a)) := by
  unfold LGraph.adj at hab
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
  rcases hab with ⟨e, he, hh⟩ | ⟨e, he, h1, _⟩
  · exact ⟨e, he, hh⟩
  · exact absurd h1 (by simp [h e he])

/-- The coloured ends of the merge of the BA reading of `Γ` are the images of those of `Γ`. -/
theorem BAAtomic_cendsMS_ofL (Γ : LGraph E I) :
    (promoteC (BAGraph.ofLGraph Γ)).merge.localReg2_cendsMS =
      localReg2_mapMS (promoteC (BAGraph.ofLGraph Γ)).vmap Γ.localReg2_cendsMS := by
  have hs : (promoteC (BAGraph.ofLGraph Γ)).merge.solid =
      ((promoteC (BAGraph.ofLGraph Γ)).solid).map (SEdge.map (promoteC (BAGraph.ofLGraph Γ)).vmap) := rfl
  unfold LGraph.localReg2_cendsMS localReg2_mapMS
  rw [hs, BAAtomic_promoteC_solid, Multiset.map_coe, List.map_map, List.map_map, List.map_map]
  rfl

/-- **The coloured path invariant along the merge at a graph without `=`-dotted edges** (both directions of
`LGraph.localReg2_pathFam_map`, along the bijection `vmap`). -/
theorem BAAtomic_pathFam_iff (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (k : ℕ) (x y : E ⊕ I) :
    Γ.localReg2_PathFam k x y ↔ (promoteC (BAGraph.ofLGraph Γ)).merge.localReg2_PathFam k
      ((promoteC (BAGraph.ofLGraph Γ)).vmap x) ((promoteC (BAGraph.ofLGraph Γ)).vmap y) := by
  set L := promoteC (BAGraph.ofLGraph Γ) with hL
  have hedge : L.merge.localReg2_edgeMS = localReg2_mapMS (fun v => L.merge.molOf (L.vmap v)) Γ.localReg2_cendsMS := by
    unfold LGraph.localReg2_edgeMS
    rw [BAAtomic_cendsMS_ofL, localReg2_mapMS_comp]
  constructor
  · intro hP
    have key := LGraph.localReg2_pathFam_map Γ L.merge L.vmap (fun a => ⟨_, BAAtomic_vmap_inl L a⟩)
      (fun v' => by
        obtain ⟨v, rfl⟩ := BAAtomic_vmap_surjective L v'
        exact ⟨v, SimpleGraph.Reachable.refl _⟩)
      (fun u v huv => by
        obtain ⟨e0, he0, h0⟩ := BAAtomic_adj_waved_of_noeq Γ h huv
        refine BAAtomic_reach_of_adj _ ((BAAtomic_merge_adj_iff (BAGraph.ofLGraph Γ) _ _).2 ⟨e0, he0, ?_⟩)
        rcases h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
        · exact Or.inr ⟨by rw [h1], by rw [h2]⟩) hP
    unfold LGraph.localReg2_PathFam
    rw [hedge]
    exact key
  · intro hP
    set e := BAAtomic_vmapEquiv Γ h with he
    have hsymm : ∀ v, e.symm (L.vmap v) = v := fun v => e.symm_apply_apply v
    have key := LGraph.localReg2_pathFam_map L.merge Γ e.symm
      (fun a => by
        obtain ⟨a0, ha0⟩ := a.2
        refine ⟨a0, e.symm_apply_eq.2 ?_⟩
        change _ = L.vmap (Sum.inl a0)
        rw [BAAtomic_vmap_inl]
        exact congrArg Sum.inl (Subtype.ext ha0).symm)
      (fun v' => ⟨e v', by rw [e.symm_apply_apply]⟩)
      (fun u v huv => by
        obtain ⟨e0, he0, h0⟩ := (BAAtomic_merge_adj_iff (BAGraph.ofLGraph Γ) _ _).1 huv
        have hadj := BAAtomic_adj_of_waved Γ (e0 := e0) he0
        rcases h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2, hsymm, hsymm]
          exact BAAtomic_reach_of_adj Γ hadj
        · rw [← h1, ← h2, hsymm, hsymm]
          exact (BAAtomic_reach_of_adj Γ hadj).symm) hP
    unfold LGraph.localReg2_PathFam
    unfold LGraph.localReg2_PathFam at hP
    have hc : localReg2_mapMS (fun v => Γ.molOf (e.symm v)) L.merge.localReg2_cendsMS = Γ.localReg2_edgeMS := by
      rw [BAAtomic_cendsMS_ofL, localReg2_mapMS_comp]
      unfold LGraph.localReg2_edgeMS
      congr 1
      funext v
      rw [hsymm]
    rw [hc, hsymm, hsymm] at key
    exact key

end OfL

/-! ## 3. `BAPathLift` -/

/-! ## 4. Compiled instances at the band lift of a concrete normal band graph -/

end RBM.Graph
