/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BAAtomic2
import RBM3D.Graph.LocalRegular2

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# The coloured path invariant at the atomic image, `BASimP'`, the shapes `s1`, `e1`, the step (part 1)

Paper: Lemma 7.17 (`lem:localregular`) (1)-(5); its proof for the band (Subappendix B.2, (B.11)
`eq:originGamma`, proof of Strategy B.1 `strat_local`); the atomic image (Definition B.3
`def_atom`); `G = Ǧ + M` (Definition B.4 `defn_normalBA`); Lemma B.6 (`lanlw`).  The path inputs
`BAShapePath` of `e2`, `macroA`, `macroB` enter as the shape binder
`∀ sh, sh = e2 ∨ sh = macroA ∨ sh = macroB → BAShapePath sh BAFrameStepTN` of `baPathStep_holds`
(continued in `baLocReg15_holds`, file 2), verbatim, with no new `Prop`.

## Contents (namespace `RBM.Graph`; private helpers carry the stem `BALocReg1`)

1. **The generic transfer** `BALocReg1_pathAt_map` (the invariant `BALocReg1_PathAt Γ k a b` =
   `PGraph.PathInv2` of the atomic image, by `Iff.rfl`):
   `LGraph.localReg2_pathFam_map` (`Graph/LocalRegular2.lean`) along a vertex map `ψ` of two BA
   graphs that respects the atoms, is onto up to molecules and maps waved edges into molecules; the
   budget moves up to the colour flip `c` (`localReg2_Fam.flip`), loops removed (`of_add_diag`) and
   loops added at a colour already present (`add_diag`).  Its three uses:
   `BALocReg1_pathAt_splitG` (an `M`-split joins atoms: the solid edges turned into `M`-dotted edges
   become loops of the image), `BALocReg1_pathAt_merge` (the merge of `=`-dotted classes), hence
   `BALocReg1_pathAt_partition` for any term `T` and `BALocReg1_pathInv2_pack` (the packed outputs
   `BAScost_pack`); `BALocReg1_pathAt_twist` (the twist flips the colours); `BALocReg1_pathAt_ext`
   (an extension term `BAGraph.ext`, the shape of the builder terms of `BAExpandW`, `BAWeightOp`)
   and `BALocReg1_pathAt_lanlwT1` (term 1 of `lanlw`: the edge `Ǧ_{xy}` becomes `G_{αy}` with `α` in
   the atom of `x`, the loop `Ǧ_{ββ}` is added at the molecule of `x`).
2. `baEquivPath_holds` (along `BAEquivC` of `Graph/BASim.lean`; one direction, the one the
   consumers read), `baPathTwist_holds` (the twist, both directions).
3. `BAShapePath`, `baShapePath_s1_tn` (vacuous), `baShapePath_e1_tn` (the `tagT1` outputs of
   `lanlwT1`), `baShapePath_twist`.  The tag lemma `BALocReg1_frameT_tags` is a copy of the private
   `BAStepS_frameT_tags` (`Graph/BAStepS.lean`) with its helpers, under the stem.
4. `BASimP'`, `baSimP'_holds` (per output, `P' := (P.twist c t).img`, `baMatch_holds` at
   `P.twist c t`).
5. `BAPathStep`, `baPathStep_of_simP'` (per output), `baPathStep_holds` (with the shape binder).

Combinatorial; no data.  The invariants are those of the band (`Graph/LocalRegular2.lean`), applied
to the atomic image.
-/

noncomputable section

namespace RBM.Graph

/-! ## 1. The coloured path invariant at the atomic image: the generic transfer along a vertex map -/

section Generic

variable {E I E' I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype E'] [DecidableEq E']
  [Fintype I'] [DecidableEq I']

/-- the molecule of the image of a vertex -/
def BALocReg1_mu (Γ : BAGraph E I) (v : E ⊕ I) : (promoteC Γ).merge.Mol :=
  (promoteC Γ).merge.molOf ((promoteC Γ).vmap v)

/-- the coloured path invariant of the atomic image of `Γ` between the external vertices `a`, `b` -/
def BALocReg1_PathAt (Γ : BAGraph E I) (k : ℕ) (a b : E) : Prop :=
  (promoteC Γ).merge.localReg2_PathFam k (Sum.inl ((promoteC Γ).extMap a)) (Sum.inl ((promoteC Γ).extMap b))

theorem BALocReg1_flip_false {N : Type*} (s : Bool × Sym2 N) : localReg2_flip false s = s := by
  obtain ⟨σ, z⟩ := s
  cases σ <;> rfl

/-- **The coloured path invariant passes along a vertex map `ψ`** between BA graphs that respects the atoms, is onto up to molecules, maps waved edges
into molecules, and maps the solid edges onto those of `Γ'` up to the colour flip `c` and loops (in the molecules of `Γ'`). -/
theorem BALocReg1_pathAt_map (Γ : BAGraph E I) (Γ' : BAGraph E' I') (ψ : E ⊕ I → E' ⊕ I') (f : E → E') (c : Bool)
    (hψ : ∀ a, ψ (Sum.inl a) = Sum.inl (f a))
    (hatom : ∀ u v, v ∈ Γ.atom u → ψ v ∈ Γ'.atom (ψ u))
    (hsurj : ∀ w, ∃ u, ψ u ∈ Γ'.mol w)
    (hwav : ∀ e ∈ Γ.waved, ψ e.y ∈ Γ'.mol (ψ e.x))
    (Bm Drem Dadd : List (Bool × Sym2 (promoteC Γ').merge.Mol)) (hDrem : ∀ s ∈ Drem, s.2.IsDiag) (hDadd : ∀ s ∈ Dadd, s.2.IsDiag)
    (hcov : ∀ s ∈ Dadd, ∀ C ∈ s.2, ∃ t ∈ Bm, t.1 = s.1 ∧ C ∈ t.2)
    (hrem : (Γ.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' (ψ e.src), BALocReg1_mu Γ' (ψ e.dst))) : List _).Perm
      ((Bm ++ Drem).map (localReg2_flip c)))
    (hadd : (Γ'.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' e.src, BALocReg1_mu Γ' e.dst)) : List _).Perm (Bm ++ Dadd))
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) : BALocReg1_PathAt Γ' k (f a) (f b) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : (promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls → E ⊕ I, ∀ w, (promoteC Γ).vmap (g w) = w :=
    ⟨Function.surjInv (BAAtomic_vmap_surjective (promoteC Γ)), Function.surjInv_eq (BAAtomic_vmap_surjective (promoteC Γ))⟩
  have hφ : ∀ u, (promoteC Γ').vmap (ψ (g ((promoteC Γ).vmap u))) = (promoteC Γ').vmap (ψ u) := by
    intro u
    have h1 : g ((promoteC Γ).vmap u) ∈ Γ.atom u := (BAAtomic_promoteC_vmap_eq_atom Γ u _).1 (hg _).symm
    exact ((BAAtomic_promoteC_vmap_eq_atom Γ' _ _).2 (hatom _ _ h1)).symm
  have hφl : ∀ a, (promoteC Γ').vmap (ψ (g (Sum.inl ((promoteC Γ).extMap a)))) = Sum.inl ((promoteC Γ').extMap (f a)) := by
    intro a
    have := hφ (Sum.inl a)
    rw [BAAtomic_vmap_inl, hψ, BAAtomic_vmap_inl] at this
    exact this
  have key := LGraph.localReg2_pathFam_map (promoteC Γ).merge (promoteC Γ').merge
    (fun w => (promoteC Γ').vmap (ψ (g w)))
    (by
      rintro ⟨q, a, rfl⟩
      exact ⟨_, hφl a⟩)
    (by
      intro v'
      obtain ⟨u', rfl⟩ := BAAtomic_vmap_surjective (promoteC Γ') v'
      obtain ⟨u, hu⟩ := hsurj u'
      refine ⟨(promoteC Γ).vmap u, ?_⟩
      rw [hφ u]
      exact (SimpleGraph.ConnectedComponent.eq (G := (promoteC Γ').merge.molGraph)).1 ((Γ'.img_molOf_eq_iff u' (ψ u)).2 hu))
    (by
      intro u v huv
      obtain ⟨e0, he0, h0 | h0⟩ := (BAAtomic_merge_adj_iff Γ u v).1 huv
      · rw [← h0.1, ← h0.2, hφ, hφ]
        exact (SimpleGraph.ConnectedComponent.eq (G := (promoteC Γ').merge.molGraph)).1 ((Γ'.img_molOf_eq_iff _ _).2 (hwav e0 he0))
      · rw [← h0.1, ← h0.2, hφ, hφ]
        exact ((SimpleGraph.ConnectedComponent.eq (G := (promoteC Γ').merge.molGraph)).1 ((Γ'.img_molOf_eq_iff _ _).2 (hwav e0 he0))).symm)
    h
  have hx : ∀ a, (promoteC Γ').vmap (ψ (g (Sum.inl ((promoteC Γ).extMap a)))) = Sum.inl ((promoteC Γ').extMap (f a)) := hφl
  unfold BALocReg1_PathAt LGraph.localReg2_PathFam
  rw [hx, hx] at key
  have hB1 : localReg2_mapMS (fun v => (promoteC Γ').merge.molOf ((promoteC Γ').vmap (ψ (g v)))) (promoteC Γ).merge.localReg2_cendsMS =
      ((Γ.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' (ψ e.src), BALocReg1_mu Γ' (ψ e.dst))) : List _) : Multiset _) := by
    unfold LGraph.localReg2_cendsMS localReg2_mapMS
    simp only [Multiset.map_coe]
    rw [show (promoteC Γ).merge.solid = (promoteC Γ).solid.map (SEdge.map (promoteC Γ).vmap) from rfl, BAAtomic_promoteC_solid]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp [SEdge.localReg2_cends, SEdge.map, Sym2.map_mk, hφ, BALocReg1_mu]
  have hB2 : (promoteC Γ').merge.localReg2_edgeMS =
      ((Γ'.solid.map fun e => (e.σ, s(BALocReg1_mu Γ' e.src, BALocReg1_mu Γ' e.dst)) : List _) : Multiset _) := by
    unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS
    simp only [Multiset.map_coe]
    rw [show (promoteC Γ').merge.solid = (promoteC Γ').solid.map (SEdge.map (promoteC Γ').vmap) from rfl, BAAtomic_promoteC_solid]
    simp only [List.map_map]
    rfl
  rw [hB1, Multiset.coe_eq_coe.2 hrem, ← Multiset.map_coe, ← Multiset.coe_add] at key
  have key2 := localReg2_Fam.flip c key
  rw [localReg2_flip_flip_ms] at key2
  have key3 := localReg2_Fam.of_add_diag (D := (Drem : Multiset _)) (fun s hs => hDrem s (Multiset.mem_coe.1 hs)) key2
  have key4 := localReg2_Fam.add_diag (D := (Dadd : Multiset _)) (fun s hs => hDadd s (Multiset.mem_coe.1 hs))
    (fun s hs C hC => by
      obtain ⟨t, ht, h1, h2⟩ := hcov s (Multiset.mem_coe.1 hs) C hC
      exact ⟨t, Multiset.mem_coe.2 ht, h1, h2⟩) key3
  rw [hB2, Multiset.coe_eq_coe.2 hadd, ← Multiset.coe_add]
  exact key4

theorem BALocReg1_flip_false_list {N : Type*} (l : List (Bool × Sym2 N)) : l.map (localReg2_flip false) = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun s _ => BALocReg1_flip_false s

/-! ### The `M`-split and the merge keep the invariant (any term `T`) -/

theorem BALocReg1_split_perm {V N : Type} (μ : V → N) (es : List (SEdge V)) : ∀ r ∈ baSplitSolid es,
    (es.map (fun e => (e.σ, s(μ e.src, μ e.dst)))).Perm
      (r.1.map (fun e => (e.σ, s(μ e.src, μ e.dst))) ++ r.2.map (fun m => (m.σ, s(μ m.x, μ m.y)))) := by
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
    have h := ih r' hr'
    cases hc : e.circ
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using h.cons (e.σ, s(μ e.src, μ e.dst))
      · simp only [List.map_cons]
        exact ((h.cons _).trans List.perm_middle.symm)
    · simp only [hc, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      simpa using h.cons (e.σ, s(μ e.src, μ e.dst))

theorem BALocReg1_atomAdj_mono {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ Γ' : BAGraph E I)
    (hd : ∀ u v, Γ.dotted.any (fun e => e.eq && decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) = true →
      Γ'.dotted.any (fun e => e.eq && decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u))) = true)
    (hp : ∀ e ∈ Γ.psi, e ∈ Γ'.psi) (hm : ∀ e ∈ Γ.mdot, e ∈ Γ'.mdot) {u v : E ⊕ I} (h : Γ.atomAdj u v = true) :
    Γ'.atomAdj u v = true := by
  unfold BAGraph.atomAdj at h ⊢
  simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with (h | ⟨e, he, h⟩) | ⟨e, he, h⟩
  · exact Or.inl (Or.inl (hd u v (by simpa [List.any_eq_true] using h)) |> fun x => by simpa [List.any_eq_true] using x)
  · exact Or.inl (Or.inr ⟨e, hp e he, h⟩)
  · exact Or.inr ⟨e, hm e he, h⟩

theorem BALocReg1_mem_mol_self {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (w : E ⊕ I) :
    w ∈ Γ.mol w := by
  rw [BAGraph.mem_mol_iff]

theorem BALocReg1_mem_mol_waved {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    {e0 : WEdge (E ⊕ I)} (he0 : e0 ∈ Γ.waved) : e0.y ∈ Γ.mol e0.x := by
  rw [BAGraph.mem_mol_iff]
  refine Relation.ReflTransGen.single ?_
  unfold BAGraph.adj
  simp [BAAtomic_adj_of_waved Γ.toLGraph he0]

/-- **The `M`-split keeps the invariant**: a term `Q'` of `splitG` of `T` (the solid edges turned into `M`-dotted edges become loops of the image). -/
theorem BALocReg1_pathAt_splitG {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (T : BAGraph E I)
    {Q' : BAGraph E I} (hQ : Q' ∈ T.splitG) {k : ℕ} {a b : E} (h : BALocReg1_PathAt T k a b) : BALocReg1_PathAt Q' k a b := by
  classical
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hQ
  set Q' : BAGraph E I := BAGraph.mk (RBM.Graph.LGraph.mk r.1 T.waved T.dotted T.coeff) T.psi (r.2 ++ T.mdot) with hQ'
  have hat : ∀ u v, v ∈ T.atom u → v ∈ Q'.atom u := by
    intro u v hv
    rw [BAGraph.mem_atom_iff] at hv ⊢
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) u v hv
    refine BALocReg1_atomAdj_mono T Q' (fun u v hh => ?_) (fun e he => he) (fun e he => List.mem_append_right _ he) hxy
    exact hh
  have hmd : ∀ m ∈ r.2, (promoteC Q').vmap m.x = (promoteC Q').vmap m.y := by
    intro m hm
    refine (BAAtomic_promoteC_vmap_eq_atom Q' _ _).2 ?_
    rw [BAGraph.mem_atom_iff]
    refine Relation.ReflTransGen.single ?_
    unfold BAGraph.atomAdj
    simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨m, List.mem_append_left _ hm, Or.inl ⟨rfl, rfl⟩⟩
  refine BALocReg1_pathAt_map T Q' id id false (fun _ => rfl) hat (fun w => ⟨w, BALocReg1_mem_mol_self Q' w⟩)
    (fun e he => BALocReg1_mem_mol_waved Q' he) (Q'.solid.map fun e => (e.σ, s(BALocReg1_mu Q' e.src, BALocReg1_mu Q' e.dst)))
    (r.2.map fun m => (m.σ, s(BALocReg1_mu Q' m.x, BALocReg1_mu Q' m.y))) [] ?_ (by simp) (by simp) ?_ (by simp) h
  · intro s hs
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hs
    simp only [BALocReg1_mu, hmd m hm]
    exact Sym2.mk_isDiag_iff.2 rfl
  · rw [BALocReg1_flip_false_list]
    exact BALocReg1_split_perm (BALocReg1_mu Q') T.solid r hr

/-- **The merge of the `=`-dotted classes keeps the invariant** (`BAGraph.merge`, the packing of `BAGraph.partition`). -/
theorem BALocReg1_pathAt_merge {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Q : BAGraph E I)
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Q k a b) :
    BALocReg1_PathAt Q.merge k (Q.toLGraph.extMap a) (Q.toLGraph.extMap b) := by
  classical
  have hrel : ∀ u v, Q.toLGraph.EqRel u v → Q.toLGraph.vmap u = Q.toLGraph.vmap v := fun u v h =>
    congrArg Q.toLGraph.vmapC (Quotient.sound (Relation.EqvGen.rel _ _ h))
  have hat : ∀ u v, v ∈ Q.atom u → Q.toLGraph.vmap v ∈ Q.merge.atom (Q.toLGraph.vmap u) := by
    intro u v hv
    rw [BAGraph.mem_atom_iff] at hv ⊢
    induction hv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      refine ih.trans ?_
      unfold BAGraph.atomAdj at hbc
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hbc
      rcases hbc with (⟨e, he, he1, he2⟩ | ⟨e, he, he2⟩) | ⟨e, he, he2⟩
      · have hr : Q.toLGraph.EqRel _ _ := ⟨e, he, he1, he2⟩
        rw [hrel _ _ hr]
      · refine Relation.ReflTransGen.single ?_
        unfold BAGraph.atomAdj
        simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
        refine Or.inl (Or.inr ⟨BAPsiEdge.map Q.toLGraph.vmap e, List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩)
        rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by simp [BAPsiEdge.map, h1], by simp [BAPsiEdge.map, h2]⟩
        · exact Or.inr ⟨by simp [BAPsiEdge.map, h1], by simp [BAPsiEdge.map, h2]⟩
      · refine Relation.ReflTransGen.single ?_
        unfold BAGraph.atomAdj
        simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
        refine Or.inr ⟨BAMEdge.map Q.toLGraph.vmap e, List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩
        rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by simp [BAMEdge.map, h1], by simp [BAMEdge.map, h2]⟩
        · exact Or.inr ⟨by simp [BAMEdge.map, h1], by simp [BAMEdge.map, h2]⟩
  refine BALocReg1_pathAt_map Q Q.merge Q.toLGraph.vmap Q.toLGraph.extMap false (fun a => BAAtomic_vmap_inl Q.toLGraph a) hat
    (fun w => by
      obtain ⟨u, rfl⟩ := BAAtomic_vmap_surjective Q.toLGraph w
      exact ⟨u, BALocReg1_mem_mol_self Q.merge _⟩)
    (fun e he => BALocReg1_mem_mol_waved Q.merge (e0 := WEdge.map Q.toLGraph.vmap e) (List.mem_map.2 ⟨e, he, rfl⟩))
    (Q.solid.map fun e => (e.σ, s(BALocReg1_mu Q.merge (Q.toLGraph.vmap e.src), BALocReg1_mu Q.merge (Q.toLGraph.vmap e.dst)))) [] []
    (by simp) (by simp) (by simp) ?_ ?_ h
  · rw [List.append_nil, BALocReg1_flip_false_list]
  · rw [List.append_nil]
    rw [show Q.merge.solid = Q.solid.map (SEdge.map Q.toLGraph.vmap) from rfl, List.map_map]
    exact List.Perm.refl _

/-- **The partition keeps the invariant** (`BAGraph.partition`: `M`-split, then merge): for any term `T`. -/
theorem BALocReg1_pathAt_partition {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (T : BAGraph E I)
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt T k a b) : ∀ Q0 ∈ T.partition, BALocReg1_PathAt Q0.g k (Q0.ext a) (Q0.ext b) := by
  intro Q0 hQ0
  obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ0
  exact BALocReg1_pathAt_merge Q' (BALocReg1_pathAt_splitG T hQ' h)

/-- the packed output `BAScost_pack P Q0` of a term `T` of `P`: the image has the path invariant if the term has -/
theorem BALocReg1_pathInv2_pack (P : BAPGraph (Fin 2)) {I'' : Type} [Fintype I''] [DecidableEq I''] (T : BAGraph P.E' I'') {k : ℕ}
    (h : BALocReg1_PathAt T k (P.ext 0) (P.ext 1)) : ∀ Q0 ∈ T.partition, (BAScost_pack P Q0).img.PathInv2 k :=
  fun Q0 hQ0 => BALocReg1_pathAt_partition T h Q0 hQ0

theorem BALocReg1_mu_eq_iff {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (u v : E ⊕ I) :
    BALocReg1_mu Γ u = BALocReg1_mu Γ v ↔ v ∈ Γ.mol u := Γ.img_molOf_eq_iff u v

theorem BALocReg1_mol_symm {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) {u v : E ⊕ I}
    (h : v ∈ Γ.mol u) : u ∈ Γ.mol v := (BALocReg1_mu_eq_iff Γ v u).1 ((BALocReg1_mu_eq_iff Γ u v).2 h).symm

theorem BALocReg1_mol_trans {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) {u v w : E ⊕ I}
    (h : v ∈ Γ.mol u) (h' : w ∈ Γ.mol v) : w ∈ Γ.mol u :=
  (BALocReg1_mu_eq_iff Γ u w).1 (((BALocReg1_mu_eq_iff Γ u v).2 h).trans ((BALocReg1_mu_eq_iff Γ v w).2 h'))

theorem BALocReg1_mol_of_atom {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) {u v : E ⊕ I}
    (h : atomSetoid Γ u v) : v ∈ Γ.mol u := Γ.atom_subset_mol u ((BAAtomic_atomSetoid_iff Γ u v).1 h)

/-- **An extension term** `BAGraph.ext n Γ rest S W md` of `Γ` (the shape of the builder terms of `BAExpandW`, `BAWeightOp`): the invariant passes from `Γ`
under the budget data `Bm`, `Drem`, `Dadd` of `BALocReg1_pathAt_map` at the vertex map `owxEmb n`; the new vertices lie in molecules of old ones. -/
theorem BALocReg1_pathAt_ext {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (n : ℕ) (Γ : BAGraph E I)
    (rest : List (SEdge (E ⊕ I))) (S : List (SEdge (E ⊕ (I ⊕ Fin n)))) (W : List (WEdge (E ⊕ (I ⊕ Fin n)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin n))))
    (hnew : ∀ i : Fin n, ∃ u : E ⊕ I, owxEmb n u ∈ (BAGraph.ext n Γ rest S W md).mol (Sum.inr (Sum.inr i))) (c : Bool)
    (Bm Drem Dadd : List (Bool × Sym2 (promoteC (BAGraph.ext n Γ rest S W md)).merge.Mol))
    (hDrem : ∀ s ∈ Drem, s.2.IsDiag) (hDadd : ∀ s ∈ Dadd, s.2.IsDiag) (hcov : ∀ s ∈ Dadd, ∀ C ∈ s.2, ∃ t ∈ Bm, t.1 = s.1 ∧ C ∈ t.2)
    (hrem : (Γ.solid.map fun e => (e.σ, s(BALocReg1_mu (BAGraph.ext n Γ rest S W md) (owxEmb n e.src),
      BALocReg1_mu (BAGraph.ext n Γ rest S W md) (owxEmb n e.dst))) : List _).Perm ((Bm ++ Drem).map (localReg2_flip c)))
    (hadd : ((BAGraph.ext n Γ rest S W md).solid.map fun e => (e.σ, s(BALocReg1_mu (BAGraph.ext n Γ rest S W md) e.src,
      BALocReg1_mu (BAGraph.ext n Γ rest S W md) e.dst)) : List _).Perm (Bm ++ Dadd))
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) : BALocReg1_PathAt (BAGraph.ext n Γ rest S W md) k a b := by
  classical
  refine BALocReg1_pathAt_map Γ (BAGraph.ext n Γ rest S W md) (owxEmb n) id c (fun _ => rfl)
    (fun u v hv => ?_) (fun w => ?_) (fun e he => ?_) Bm Drem Dadd hDrem hDadd hcov hrem hadd h
  · exact (BAAtomic_atomSetoid_iff _ _ _).1 (BAScost_atomSetoid_ext Γ rest S W md ((BAAtomic_atomSetoid_iff Γ u v).2 hv))
  · rcases w with a | i | j
    · exact ⟨Sum.inl a, BALocReg1_mem_mol_self _ _⟩
    · exact ⟨Sum.inr i, BALocReg1_mem_mol_self _ _⟩
    · exact hnew j
  · exact BALocReg1_mem_mol_waved (BAGraph.ext n Γ rest S W md) (e0 := WEdge.map (owxEmb n) e) (List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩))

/-- **The first term of `lanlw`** (`BAGraph.lanlwT1`): the edge `Ǧ_{xy}` becomes `G_{αy}` with `α` in the atom of `x`, and the loop `Ǧ_{ββ}` is added at the molecule of `x`
(the colour blue is present there, the edge `Ǧ_{xy}`). -/
theorem BALocReg1_pathAt_lanlwT1 {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) {k : ℕ} {a b : E}
    (h : BALocReg1_PathAt Γ k a b) : BALocReg1_PathAt (BAGraph.lanlwT1 Γ p) k a b := by
  classical
  rw [BAScost_lanlwT1_eq]
  set T := BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] with hT
  have hmd : atomSetoid T (owxEmb 2 p.1.src) (bpv 0) :=
    BAScost_atomSetoid_ext_md Γ p.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp)
  have hα : (bpv 0 : E ⊕ (I ⊕ Fin 2)) ∈ T.mol (owxEmb 2 p.1.src) := BALocReg1_mol_of_atom T hmd
  have hβ : (bpv 1 : E ⊕ (I ⊕ Fin 2)) ∈ T.mol (owxEmb 2 p.1.src) :=
    BALocReg1_mol_trans T hα (BALocReg1_mem_mol_waved T (e0 := bpW false (bpv 0) (bpv 1)) (by simp [hT, BAGraph.ext, LGraph.owxExt]))
  have hperm0 : Γ.solid.Perm (p.1 :: p.2) := lwSplit_perm Γ.solid p hp
  have hmuα : BALocReg1_mu T (bpv 0) = BALocReg1_mu T (owxEmb 2 p.1.src) := (BALocReg1_mu_eq_iff T _ _).2 (BALocReg1_mol_symm T hα)
  have hmuβ : BALocReg1_mu T (bpv 1) = BALocReg1_mu T (owxEmb 2 p.1.src) := (BALocReg1_mu_eq_iff T _ _).2 (BALocReg1_mol_symm T hβ)
  set F : SEdge (E ⊕ I) → Bool × Sym2 (promoteC T).merge.Mol :=
    fun e => (e.σ, s(BALocReg1_mu T (owxEmb 2 e.src), BALocReg1_mu T (owxEmb 2 e.dst))) with hF
  refine BALocReg1_pathAt_ext 2 Γ p.2 _ _ _ (fun i => ?_) false (Γ.solid.map F) []
    [(true, s(BALocReg1_mu T (bpv 1), BALocReg1_mu T (bpv 1)))] (by simp) (by simp [Sym2.mk_isDiag_iff]) ?_ ?_ ?_ h
  · fin_cases i
    · exact ⟨p.1.src, BALocReg1_mol_symm T hα⟩
    · exact ⟨p.1.src, BALocReg1_mol_symm T hβ⟩
  · intro s hs C hC
    simp only [List.mem_singleton] at hs
    subst hs
    refine ⟨F p.1, List.mem_map.2 ⟨p.1, hperm0.symm.subset (List.mem_cons_self), rfl⟩, hp1.1, ?_⟩
    simp only [Sym2.mem_iff, or_self] at hC
    subst hC
    simp [hF, hmuβ]
  · rw [List.append_nil, BALocReg1_flip_false_list]
  · have hs : T.solid = p.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] := rfl
    change (T.solid.map fun e => (e.σ, s(BALocReg1_mu T e.src, BALocReg1_mu T e.dst))).Perm _
    rw [hs, List.map_append]
    have hl : ((p.2.map (SEdge.map (owxEmb 2))).map fun e => (e.σ, s(BALocReg1_mu T e.src, BALocReg1_mu T e.dst))) = p.2.map F := by
      rw [List.map_map]; rfl
    have hαy : (((bpS false (bpv 0) (owxEmb 2 p.1.dst) : SEdge _).σ, s(BALocReg1_mu T (bpS false (bpv 0) (owxEmb 2 p.1.dst) : SEdge _).src,
        BALocReg1_mu T (bpS false (bpv 0) (owxEmb 2 p.1.dst) : SEdge _).dst)) : Bool × Sym2 (promoteC T).merge.Mol) = F p.1 := by
      simp [hF, bpS, hp1.1, hmuα]
    rw [hl]
    simp only [List.map_cons, List.map_nil]
    rw [hαy]
    refine List.Perm.trans ?_ (List.Perm.append_right _ (hperm0.map F)).symm
    rw [List.map_cons, List.cons_append]
    refine List.Perm.trans ?_ (List.perm_append_singleton _ _)
    rw [List.append_assoc]
    exact List.Perm.refl _

/-- **The twist keeps the invariant** (the colours of the walks flip by `c`; `lwSymmTwistG_adj`, `SEdge.localReg2_cends_twist`, `BAGraph.BASymm1_twist_atom`). -/
theorem BALocReg1_pathAt_twist {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : BAGraph E I)
    {k : ℕ} {a b : E} (h : BALocReg1_PathAt Γ k a b) : BALocReg1_PathAt (Γ.twist c t) k a b := by
  classical
  have hadj : (Γ.twist c t).adj = Γ.adj := by
    funext u v
    unfold BAGraph.adj
    rw [show (Γ.twist c t).toLGraph.adj = Γ.toLGraph.adj from lwSymmTwistG_adj c t _, BAGraph.twist_atomAdj]
  have hsol : (Γ.twist c t).solid = Γ.solid.map (lwSymmTwistS c t) := lwSymmTwistG_solid c t Γ.toLGraph
  refine BALocReg1_pathAt_map Γ (Γ.twist c t) id id c (fun _ => rfl)
    (fun u v hv => by rw [BAGraph.BASymm1_twist_atom]; exact hv) (fun w => ⟨w, BALocReg1_mem_mol_self _ w⟩)
    (fun e he => ?_) ((Γ.twist c t).solid.map fun e => (e.σ, s(BALocReg1_mu (Γ.twist c t) e.src, BALocReg1_mu (Γ.twist c t) e.dst))) [] []
    (by simp) (by simp) (by simp) ?_ (by simp) h
  · rw [BAGraph.mem_mol_iff]
    refine Relation.ReflTransGen.single ?_
    rw [hadj]
    unfold BAGraph.adj
    simp [BAAtomic_adj_of_waved Γ.toLGraph he]
  · rw [List.append_nil, hsol, List.map_map, List.map_map]
    refine List.Perm.of_eq (List.map_congr_left fun e _ => ?_)
    have := SEdge.localReg2_cends_twist c t e
    simp only [Function.comp_apply]
    have h2 : (Prod.map id (Sym2.map (BALocReg1_mu (Γ.twist c t)))) (lwSymmTwistS c t e).localReg2_cends =
        localReg2_flip c ((Prod.map id (Sym2.map (BALocReg1_mu (Γ.twist c t)))) e.localReg2_cends) := by
      rw [this]
      obtain ⟨σ', z'⟩ := e.localReg2_cends
      rfl
    change _ = localReg2_flip c ((Prod.map id (Sym2.map (BALocReg1_mu (Γ.twist c t)))) (lwSymmTwistS c t e).localReg2_cends)
    rw [h2, localReg2_flip_flip]
    rfl

end Generic

/-! ## 2. The transfer tools -/

section Tools

theorem BALocReg1_forall₂_mem {α β : Type*} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
    ∀ a ∈ l, ∃ b ∈ l', R a b
  | _, _, .nil, a, ha => absurd ha List.not_mem_nil
  | _, _, .cons h hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | m
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := BALocReg1_forall₂_mem hs a m
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem BALocReg1_ends {V W : Type*} (φ : V → W) {x y u v : V} {x' y' : W}
    (h1 : (φ x = x' ∧ φ y = y') ∨ (φ x = y' ∧ φ y = x')) (h2 : (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    (x' = φ u ∧ y' = φ v) ∨ (x' = φ v ∧ y' = φ u) := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- **Relabelling**: the coloured path invariant passes along `BAEquivC` (`LGraph.localReg2_pathFam_map`, along the bijection of the vertices;
the solid edges agree up to order, the waved edges and `=`-dotted edges up to their ends). -/
theorem baEquivPath_holds (R S : PGraph (Fin 2)) (hRS : R.BAEquivC S) (k : ℕ) (h : R.PathInv2 k) : S.PathInv2 k := by
  classical
  obtain ⟨eE, eI, hext, hsol, ⟨l, hl, hF⟩, hd1, hd2⟩ := hRS
  have hadj : ∀ u v, R.g.adj u v = true → S.g.molGraph.Reachable (Sum.map eE eI u) (Sum.map eE eI v) := by
    intro u v huv
    refine BAAtomic_reach_of_adj S.g ?_
    unfold LGraph.adj at huv ⊢
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at huv ⊢
    rcases huv with ⟨e, he, hh⟩ | ⟨d, hd, hdeq, hh⟩
    · have hm : WEdge.map (Sum.map eE eI) e ∈ l := hl.mem_iff.2 (List.mem_map.2 ⟨e, he, rfl⟩)
      obtain ⟨e', he', hs⟩ := BALocReg1_forall₂_mem hF _ hm
      exact Or.inl ⟨e', he', BALocReg1_ends (Sum.map eE eI) hs hh⟩
    · obtain ⟨d', hd', hs1, hs2⟩ := hd1 (DEdge.map (Sum.map eE eI) d) (List.mem_map.2 ⟨d, hd, rfl⟩)
      exact Or.inr ⟨d', hd', by rw [← hs1]; exact hdeq, BALocReg1_ends (Sum.map eE eI) hs2 hh⟩
  have key := LGraph.localReg2_pathFam_map R.g S.g (Sum.map eE eI) (fun a => ⟨eE a, rfl⟩)
    (fun v' => ⟨Sum.map eE.symm eI.symm v', by
      have : Sum.map eE eI (Sum.map eE.symm eI.symm v') = v' := by cases v' <;> simp
      rw [this]⟩) hadj h
  have hbud : localReg2_mapMS (fun v => S.g.molOf (Sum.map eE eI v)) R.g.localReg2_cendsMS = S.g.localReg2_edgeMS := by
    unfold LGraph.localReg2_edgeMS LGraph.localReg2_cendsMS localReg2_mapMS
    simp only [Multiset.map_coe]
    refine Multiset.coe_eq_coe.2 ?_
    have h1 := (show (R.g.relabel (Sum.map eE eI)).solid.Perm S.g.solid from hsol).map SEdge.localReg2_cends
    have h2 := h1.map (Prod.map id (Sym2.map S.g.molOf))
    rw [show (R.g.relabel (Sum.map eE eI)).solid = R.g.solid.map (SEdge.map (Sum.map eE eI)) from rfl] at h2
    simp only [List.map_map] at h2 ⊢
    refine List.Perm.trans (List.Perm.of_eq ?_) h2
    refine List.map_congr_left fun e _ => ?_
    simp [SEdge.localReg2_cends, SEdge.map, Sym2.map_mk]
  unfold PGraph.PathInv2 LGraph.localReg2_PathFam
  rw [hbud] at key
  rw [hext, hext]
  exact key

/-- **The twist**: the image of the twist carries the coloured path invariant iff the image does (the twist is an involution). -/
theorem baPathTwist_holds (c t : Bool) (P : BAPGraph (Fin 2)) (k : ℕ) : (P.twist c t).img.PathInv2 k ↔ P.img.PathInv2 k := by
  constructor
  · intro h
    have h2 := BALocReg1_pathAt_twist c t (P.g.twist c t) (k := k) (a := P.ext 0) (b := P.ext 1) h
    rwa [BAGraph.twist_invol] at h2
  · exact fun h => BALocReg1_pathAt_twist c t P.g h

end Tools

/-! ## 3. The shapes `s1`, `e1`; the tags of a frame step

The three helper lemmas of `Graph/BAStepS.lean` (`BAStepS_tagStd_ne` ... `BAStepS_frameT_tags`, private there) are copied under the stem `BALocReg1_`. -/

section Shapes

private theorem BALocReg1_tagStd_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℕ)
    (T' : BAGraph E (I ⊕ Fin k)) : Γ.tagStd k T' ≠ BAShape.s1 ∧ Γ.tagStd k T' ≠ BAShape.e1 := by
  unfold BAGraph.tagStd
  split_ifs <;> simp

private theorem BALocReg1_tagT1_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (T' : BAGraph E (I ⊕ Fin 2)) : Γ.tagT1 T' ≠ BAShape.s1 := by
  unfold BAGraph.tagT1
  split_ifs <;> simp

/-- the outputs of `outsT` with a tag that is neither `s1` nor `e1` -/
private theorem BALocReg1_outsT_ne (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (hs : ∀ T', tg T' ≠ BAShape.s1 ∧ tg T' ≠ BAShape.e1) :
    ∀ x ∈ P.outsT tg Ts, x.1 ≠ BAShape.s1 ∧ x.1 ≠ BAShape.e1 := by
  rintro ⟨t, Q⟩ hx
  obtain ⟨T, -, T', -, rfl, -⟩ := BASim_mem_outsT P tg Ts t Q hx
  exact hs T'

/-- an `e1` output of `outsT` is a packed term of the partition of an element of `Ts`; no output is tagged `s1` -/
private theorem BALocReg1_outsT_pack (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (hs : ∀ T', tg T' ≠ BAShape.s1) :
    ∀ x ∈ P.outsT tg Ts, x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ T ∈ Ts, ∃ Q0 ∈ T.partition, x.2 = BAScost_pack P Q0) := by
  rintro ⟨t, Q⟩ hx
  obtain ⟨T, hT, T', hT', rfl, rfl⟩ := BASim_mem_outsT P tg Ts t Q hx
  exact ⟨hs T', fun _ => ⟨T, hT, T'.packMerge, List.mem_map.2 ⟨T', hT', rfl⟩, rfl⟩⟩

/-- the tags of the outputs of a `BAFrameStepT`: none is `s1`; an `e1` output is a packed term of `lanlwT1 P.g p` at a blue circled edge `p` -/
private theorem BALocReg1_frameT_tags {P : BAPGraph (Fin 2)} {LT : List (BAShape × BAPGraph (Fin 2))} (h : BAFrameStepT P LT) :
    ∀ x ∈ LT, x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
      ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := by
  have hstd : ∀ (k : ℕ) (Ts : List (BAGraph P.E' (P.I' ⊕ Fin k))) (x : BAShape × BAPGraph (Fin 2)), x ∈ P.outsT (P.g.tagStd k) Ts →
      x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
        ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := fun k Ts x hx =>
    ⟨(BALocReg1_outsT_ne P _ Ts (BALocReg1_tagStd_ne P.g k) x hx).1, fun h1 => absurd h1 (BALocReg1_outsT_ne P _ Ts (BALocReg1_tagStd_ne P.g k) x hx).2⟩
  have hconst : ∀ (sh : BAShape), sh ≠ BAShape.s1 → sh ≠ BAShape.e1 → ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I'))
      (x : BAShape × BAPGraph (Fin 2)), x ∈ P.outsT (fun _ => sh) Ts →
      x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
        ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := fun sh h1 h2 {I'} _ _ Ts x hx =>
    ⟨(BALocReg1_outsT_ne P _ Ts (fun _ => ⟨h1, h2⟩) x hx).1, fun h3 => absurd h3 (BALocReg1_outsT_ne P _ Ts (fun _ => ⟨h1, h2⟩) x hx).2⟩
  have ht1 : ∀ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) → ∀ (x : BAShape × BAPGraph (Fin 2)),
      x ∈ P.outsT P.g.tagT1 [BAGraph.lanlwT1 P.g p] → x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
        ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := by
    intro p hp hp1 x hx
    obtain ⟨h1, h2⟩ := BALocReg1_outsT_pack P _ _ (BALocReg1_tagT1_ne P.g) x hx
    refine ⟨h1, fun he => ?_⟩
    obtain ⟨T, hT, Q0, hQ0, hxe⟩ := h2 he
    rw [List.mem_singleton] at hT
    subst hT
    exact ⟨p, hp, hp1, Q0, hQ0, hxe⟩
  cases h with
  | weight p hp h =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hstd _ _ x hx
    · exact hstd _ _ x hx
  | within p hp h =>
    intro x hx
    simp only [BAPGraph.withinOutsT, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hstd _ _ x hx
    · exact hconst _ (by decide) (by decide) _ x hx
    · exact hconst _ (by decide) (by decide) _ x hx
  | edge p hp h x hx hwf hv hint hbad =>
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact ht1 p hp h y hy
    · exact hstd _ _ y hy
  | gg p hp q hq h x hx hwf hint hnb =>
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hstd _ _ y hy
    · exact hstd _ _ y hy
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    intro y hy
    simp only [BAPGraph.splitOutsT, List.mem_append] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · exact ht1 p hp ⟨h.1, h.2.1⟩ y hy
    · exact hstd _ _ y hy
    · exact hstd _ _ y hy
    · exact hconst _ (by decide) (by decide) _ y hy
    · exact hconst _ (by decide) (by decide) _ y hy
    · exact hconst _ (by decide) (by decide) _ y hy


/-- **The path invariant at a BA-only shape** (`img P` as `P.img`): the outputs of `sh` carry the invariant of the parent. -/
def BAShapePath (sh : BAShape) (T : BTStep) : Prop :=
  ∀ P LT, T P LT → ∀ Q, (sh, Q) ∈ LT → ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- `BAShapePath s1` is vacuous: no constructor of `BAFrameStepT` tags an output `s1` (as `baShapeLL_s1_tn` in `Graph/BAStepS.lean`). -/
theorem baShapePath_s1_tn : BAShapePath BAShape.s1 BAFrameStepTN := by
  rintro P LT ⟨-, hF⟩ Q hQ
  exact absurd rfl (BALocReg1_frameT_tags hF _ hQ).1

/-- **`BAShapePath e1 BAFrameStepTN`**: an `e1` output is a packed term of the partition of `lanlwT1` at a blue circled edge (`BALocReg1_frameT_tags`); the invariant passes
to `lanlwT1` (`BALocReg1_pathAt_lanlwT1`) and to its partition (`BALocReg1_pathAt_partition`). -/
theorem baShapePath_e1_tn : BAShapePath BAShape.e1 BAFrameStepTN := by
  rintro P LT ⟨-, hF⟩ Q hQ k hk
  obtain ⟨p, hp, ⟨hp1, hp2⟩, Q0, hQ0, rfl⟩ := (BALocReg1_frameT_tags hF _ hQ).2 rfl
  exact BALocReg1_pathInv2_pack P (BAGraph.lanlwT1 P.g p) (BALocReg1_pathAt_lanlwT1 P.g p hp ⟨hp1, hp2⟩ hk) Q0 hQ0

/-- the shape lemma of a frame step carries to the twisted step (as `baShapeLL_twist` in `Graph/BAStepS.lean`) -/
theorem baShapePath_twist : ∀ sh : BAShape, BAShapePath sh BAFrameStepTN → BAShapePath sh BALocStepT := by
  intro sh h P LT ⟨hN, c, t, LT0, hF, hLT⟩ Q hQ k hk
  subst hLT
  obtain ⟨⟨sh', Q0⟩, hmem, he⟩ := List.mem_map.1 hQ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact (baPathTwist_holds c t Q0 k).2 (h (P.twist c t) LT0 ⟨(ba_twist_inv_out c t P.g).2.2.2.2.2 hN, hF⟩ Q0 hmem k
    ((baPathTwist_holds c t P k).2 hk))

end Shapes

/-! ## 4. `BASimP'` and the step -/

section Step

/-- **The path half of the simulation, `BASimP'`** (as `BASimC'` in `Graph/BAStepS.lean`): the band step is chosen per output, `P'` per step. -/
def BASimP' (m : ℂ) (T : BTStep) : Prop :=
  ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), (∀ k : ℕ, P.img.PathInv2 k → P'.PathInv2 k) ∧
    ∀ Q : BAPGraph (Fin 2), (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧
      ∃ R ∈ L', ∀ k : ℕ, R.PathInv2 k → Q.img.PathInv2 k

/-- **`baSimP'_holds`**: take `P' := (P.twist c t).img`; for each `band` output, `baMatch_holds` at `P.twist c t`; the invariant moves by `baEquivPath_holds` and `baPathTwist_holds`. -/
theorem baSimP'_holds (m : ℂ) : BASimP' m BALocStepT := by
  rintro P LT ⟨hN, c, t, LT0, hF, rfl⟩
  have hN2 : (P.twist c t).g.Normal := (ba_twist_inv_out c t P.g).2.2.2.2.2 hN
  refine ⟨(P.twist c t).img, fun k hk => (baPathTwist_holds c t P k).2 hk, fun Q hQ => ?_⟩
  obtain ⟨⟨sh, Q0⟩, hmem, he⟩ := List.mem_map.1 hQ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨L', hst, R, hR, hRE⟩ := baMatch_holds m (P.twist c t) LT0 hF hN2 Q0 hmem
  exact ⟨L', hst, R, hR, fun k hRk => (baPathTwist_holds c t Q0 k).2
    (baEquivPath_holds R Q0.img (PGraph.BASim_BAEquiv_toC hRE) k hRk)⟩

/-- **The path statement of the step**: the invariant passes along a BA step. -/
def BAPathStep (BStep : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)) → Prop) : Prop :=
  ∀ P L, BStep P L → ∀ k : ℕ, P.img.PathInv2 k → ∀ Q ∈ L, Q.img.PathInv2 k

/-- **The step from a simulation** (per output): the `band` outputs by `pathInv2_locStep` (`Graph/LocalRegular2.lean`) at the band step of `BASimP'`, the others by the shapes. -/
theorem baPathStep_of_simP' (m : ℂ) (T : BTStep) (hS : BASimP' m T) (hX : ∀ sh, sh ≠ BAShape.band → BAShapePath sh T) :
    BAPathStep (untag T) := by
  rintro P L ⟨LT, hT, rfl⟩ k hk Q hQ
  obtain ⟨⟨sh, Q⟩, hmem, rfl⟩ := List.mem_map.1 hQ
  by_cases hb : sh = BAShape.band
  · subst hb
    obtain ⟨P', hc, hR⟩ := hS P LT hT
    obtain ⟨L', hst, R, hR', hRQ⟩ := hR Q hmem
    exact hRQ k (pathInv2_locStep hst (hc k hk) R hR')
  · exact hX sh hb P LT hT Q hmem k hk

/-- **The path statement of the tagged BA step**: the shapes `e2`, `macroA`, `macroB` are the hypothesis `hX`; `s1` and `e1`
are proved above. -/
theorem baPathStep_holds (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
    BAPathStep (untag BALocStepT) := by
  refine baPathStep_of_simP' 0 BALocStepT (baSimP'_holds 0) fun sh hsh => baShapePath_twist sh ?_
  cases sh with
  | band => exact absurd rfl hsh
  | s1 => exact baShapePath_s1_tn
  | e1 => exact baShapePath_e1_tn
  | e2 => exact hX _ (Or.inl rfl)
  | macroA => exact hX _ (Or.inr (Or.inl rfl))
  | macroB => exact hX _ (Or.inr (Or.inr rfl))

end Step

end RBM.Graph

end
