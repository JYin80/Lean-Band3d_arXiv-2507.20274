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

section Lift

/-- The graph of the BA-normal lift of a band graph: every solid edge circled. -/
def liftG (P : PGraph (Fin 2)) : LGraph P.E' P.I' := { P.g with solid := P.g.solid.map fun e => { e with circ := true } }

/-- The BA-normal lift of a packed band graph: every solid edge circled, no `Ψ`- or `M`-dotted edge (the instance of the pins at the band). -/
def liftC (P : PGraph (Fin 2)) : BAPGraph (Fin 2) where
  E' := P.E'
  I' := P.I'
  ext := P.ext
  ext_surj := P.ext_surj
  g := BAGraph.ofLGraph (liftG P)

theorem liftC_normal (P : PGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) : (liftC P).g.Normal :=
  ⟨hD, fun e he => by obtain ⟨e0, _, rfl⟩ := List.mem_map.1 he; rfl⟩

end Lift

/-! ## 2. Without `=`-dotted edges every atom is a vertex -/

section OfL

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Without `=`-dotted edges every atom is a vertex (`BAVocab.lean`, private `BAVocab_atom_ofL`; copied from T2397 probe 130). -/
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
  have h1 := (promoteC_vmap_eq_iff _ u v).1 huv
  rw [BAAtomic_atom_ofL Γ h, Finset.mem_singleton] at h1
  exact h1.symm

/-- The vertices of the merge of the BA reading of `Γ` are those of `Γ`. -/
def BAAtomic_vmapEquiv (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) :
    E ⊕ I ≃ (promoteC (BAGraph.ofLGraph Γ)).ExtCls ⊕ (promoteC (BAGraph.ofLGraph Γ)).IntCls :=
  Equiv.ofBijective _ ⟨BAAtomic_vmap_injective_ofL Γ h, BAAtomic_vmap_surjective _⟩

theorem BAAtomic_vmapEquiv_apply (Γ : LGraph E I) (h : ∀ e ∈ Γ.dotted, e.eq = false) (v : E ⊕ I) :
    BAAtomic_vmapEquiv Γ h v = (promoteC (BAGraph.ofLGraph Γ)).vmap v := rfl

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
  rw [hs, promoteC_solid, Multiset.map_coe, List.map_map, List.map_map, List.map_map]
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

section PathLift

theorem BAAtomic_cendsMS_liftG (P : PGraph (Fin 2)) : (liftG P).localReg2_cendsMS = P.g.localReg2_cendsMS := by
  unfold LGraph.localReg2_cendsMS liftG
  rw [List.map_map]
  rfl

theorem BAAtomic_pathFam_liftG (P : PGraph (Fin 2)) (k : ℕ) (x y : P.E' ⊕ P.I') :
    (liftG P).localReg2_PathFam k x y ↔ P.g.localReg2_PathFam k x y := by
  unfold LGraph.localReg2_PathFam LGraph.localReg2_edgeMS
  rw [BAAtomic_cendsMS_liftG]
  exact Iff.rfl

/-- **Map property (BAPathLift)** (T2397 probe 355, row L3b-S1, conservativity): at a normal band graph the image of the lift has the path
invariant of the graph (`localReg2_pathFam_map`). -/
def BAPathLift : Prop :=
  ∀ P0 : PGraph (Fin 2), P0.g.Normal → ∀ k, (BAPGraph.img (liftC P0)).PathInv2 k ↔ P0.PathInv2 k

theorem BAPathLift_holds : BAPathLift := by
  intro P0 hN k
  have h := BAAtomic_pathFam_iff (liftG P0) hN.1 k (Sum.inl (P0.ext 0)) (Sum.inl (P0.ext 1))
  rw [BAAtomic_pathFam_liftG, BAAtomic_vmap_inl, BAAtomic_vmap_inl] at h
  exact h.symm

/-- The image of the lift has the counters of the band graph (the counters `(n_S, n_W, n_V, n_M)` of the lift are those of `P0` and the
atoms of the lift are its vertices). -/
theorem BAAtomic_counters_liftC (P0 : PGraph (Fin 2)) (hD : ∀ e ∈ P0.g.dotted, e.eq = false) :
    (BAPGraph.img (liftC P0)).g.counters = P0.g.counters := by
  have h1 : (BAPGraph.img (liftC P0)).g.counters = (liftC P0).g.counters := BAImgCounters_holds (liftC P0)
  have h2 : (liftC P0).g.counters = (liftG P0).counters := BAGraph.counters_ofLGraph (liftG P0) hD
  rw [h1, h2]
  simp [liftG, LGraph.counters, LGraph.nS, LGraph.nW, LGraph.nV, LGraph.nM]
  rfl

end PathLift

/-! ## 4. Compiled instances at the band lift of a concrete normal band graph -/

section Instances

/-- `p2Graph` (`(eq:p=2graph)`, `LWVocab.lean:191`: `E = Fin 2`, `I = Fin 4`, six solid edges, two waved edges, four `×`-dotted edges) is
a normal band graph. -/
private theorem BAAtomic_p2_normal : p2Graph.pack.g.Normal := by decide

/-- `BAPathLift` at `P0 = p2Graph.pack`, for every `k`. -/
example (k : ℕ) : (BAPGraph.img (liftC p2Graph.pack)).PathInv2 k ↔ p2Graph.pack.PathInv2 k :=
  BAPathLift_holds p2Graph.pack BAAtomic_p2_normal k

/-- The lift of `p2Graph` is BA-normal, with six solid edges, two waved edges and no `Ψ`- or `M`-dotted edge. -/
example : (liftC p2Graph.pack).g.Normal ∧ (liftC p2Graph.pack).g.solid.length = 6 ∧ (liftC p2Graph.pack).g.waved.length = 2 ∧
    (liftC p2Graph.pack).g.psi = [] ∧ (liftC p2Graph.pack).g.mdot = [] :=
  ⟨liftC_normal _ BAAtomic_p2_normal.1, rfl, rfl, rfl, rfl⟩

/-- (m0) at the lift: the image is normal and a solid edge is circled iff it is a loop. -/
example : (BAPGraph.img (liftC p2Graph.pack)).g.Normal ∧ LGraph.CircIffLoop (BAPGraph.img (liftC p2Graph.pack)).g :=
  BAImgNormal_holds (liftC p2Graph.pack) (liftC_normal _ BAAtomic_p2_normal.1)

/-- (m1) at the lift: the image has the counters of the lift, and those of `p2Graph`. -/
example : (BAPGraph.img (liftC p2Graph.pack)).g.counters = (liftC p2Graph.pack).g.counters ∧
    (BAPGraph.img (liftC p2Graph.pack)).g.counters = p2Graph.counters :=
  ⟨BAImgCounters_holds (liftC p2Graph.pack), BAAtomic_counters_liftC p2Graph.pack BAAtomic_p2_normal.1⟩

/-- (m2) at the lift. -/
example (u v : (liftC p2Graph.pack).E' ⊕ (liftC p2Graph.pack).I') :
    (promoteC (liftC p2Graph.pack).g).merge.molOf ((promoteC (liftC p2Graph.pack).g).vmap u) =
      (promoteC (liftC p2Graph.pack).g).merge.molOf ((promoteC (liftC p2Graph.pack).g).vmap v) ↔ v ∈ (liftC p2Graph.pack).g.mol u :=
  BAImgMol_holds (liftC p2Graph.pack) u v

/-- `BAimg` at the lift (every deterministic hypothesis discharged). -/
example : (liftC p2Graph.pack).g.img.g.counters = (liftC p2Graph.pack).g.counters ∧
    (liftC p2Graph.pack).g.img.g.lvl1NLoops = (liftC p2Graph.pack).g.nLoops ∧
    (liftC p2Graph.pack).g.img.g.lvl1NPairs = (liftC p2Graph.pack).g.nPairs ∧
    Fintype.card (liftC p2Graph.pack).g.img.E' = (liftC p2Graph.pack).g.nExt ∧
    ((liftC p2Graph.pack).g.Normal → (liftC p2Graph.pack).g.img.g.Normal) ∧
    ((liftC p2Graph.pack).g.Normal → ((liftC p2Graph.pack).g.LocStd ↔ (liftC p2Graph.pack).g.img.g.LocStd)) :=
  BAimg_holds (liftC p2Graph.pack).g

end Instances

end RBM.Graph
