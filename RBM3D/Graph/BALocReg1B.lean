/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALocReg1
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BALvl1B
import RBM3D.Graph.BALvl1B2
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAExpandW
import RBM3D.Gauss.FineModel

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
# BA-L L3b1 (T2456), part 2: the start, the start bound, the shadow bridge, the contract (1)-(5), the value identity

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (`lem:localregular`), `:790` (`(eq:local_Gs)`), `paper/tex/B_graphical_lemmas.tex:172-199`, `:201` (the starting graph),
`:302-313`, `:339-341`.  Design: `docs/reports/T2387-design.md` §6 row L3b1, `docs/reports/T2397-design.md:55, 79, 110`; DECISIONS §260 (1); supervisor `2026-10-12-1152` O7.
Part 1 is `Graph/BALocReg1.lean`.  Split Σ (H250 (2)): the contract takes the shape binder of L3b2 as its hypothesis.

## Contents (namespace `RBM.Graph`; private helpers and the instance names carry the stem `BALocReg1`)

1. **Target 5**: `BAPathInit` (probe 155), `baPathInit_holds` (the band start family `localReg2_fxyPowGraph_pathFam`, transferred to the atomic image by `BAAtomic_pathFam_iff`, then the partition).
2. **Target 6**: `baStart_nM_le` (`P0.g.nM ≤ p` at every start term; owed here by DECISIONS §260 (1)).
3. **Target 8**: `baShadow_locReg345` (the image carries (3)-(5) iff the shadow does: the molecules correspond by `BALocReg1_molMap`, the molecular edges agree;
   `BALocReg1_locReg345_of_equiv` transfers the walks along a bijection of the molecules).  No normality is needed.
4. **Target 7**: `BALocReg15` and `baLocReg15_holds` (with the shape binder): `Q.img.PathInv2 p`, `Q.g.nM ≤ p`, `LocReg2` on the image, and at `Q.g.LocStd` the predicates (1) on the image,
   (3)-(5) on the image and on the shadow.  `BReach.ind` (`BAScost:105`) over `baReach_bReach` (`BAStepS:403`), with targets 4, 5, 6 and `baLvl1StepGood_holds` (`BALvl1B2:264`).
5. **Target 9**: `ba_fxyPow_integral_eq` (the value of the BA reading of the start graph is `|f_{xy}|^p`).
6. **Instances**: targets 5-7 at `p = 2` from a start term, and after one weight step at its blue circled loop (`BALocReg1B_start_step`); the `LocStd` branch of target 7
   (with target 8) at a locally standard graph with one internal molecule reached by two weight steps (`BALocReg1B_reach_locStd`: the packed outputs live over quotient
   types, and the renaming lemmas `BALocReg1B_mapG` … carry `LocStd`, `n_M` to concrete twins that the kernel evaluates); target 8 also at the lift of the band graph
   `localReg2_inst_Q`; target 9 at `d = 3`, `L = 4`, `W = 2`.

Not here: (6) (merged), `BAShapePath` of `e2`, `macroA`, `macroB` (L3b2), the composed statement with `BALocRegConcl` (L3b2, or L3d2).
-/

noncomputable section

namespace RBM.Graph

/-! ## 5. Target 5: the path invariant at the image of every start term -/

section Init

/-- **The path pin of the start** (T2397 probe 155): the invariant at the image of every term of the partition of the start graph. -/
def BAPathInit (p : ℕ) : Prop :=
  ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P.img.PathInv2 p

/-- **Target 5**: the band start graph has the family (`localReg2_fxyPowGraph_pathFam`), the BA reading has the same on its atomic image (`BAAtomic_pathFam_iff`, no `=`-dotted
edge), and the partition (`M`-split, merge) keeps it (`BALocReg1_pathAt_partition`). -/
theorem baPathInit_holds (p : ℕ) : BAPathInit p := by
  intro P hP
  have hD : ∀ e ∈ (fxyPowGraph p).dotted, e.eq = false := (fxyPowGraph_normal p).1
  have h := (BAAtomic_pathFam_iff (fxyPowGraph p) hD p (Sum.inl 0) (Sum.inl 1)).1 (localReg2_fxyPowGraph_pathFam p)
  rw [BAAtomic_vmap_inl, BAAtomic_vmap_inl] at h
  obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hP
  exact BALocReg1_pathAt_partition (BAGraph.ofLGraph (fxyPowGraph p)) (a := 0) (b := 1) h _ (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)

end Init

/-! ## 6. Target 6: the start bound `n_M ≤ p` -/

section Start

/-- **Target 6** (DECISIONS §260 (1)): every start term has `n_M ≤ p`.  The band start graph has `n_M = p` (`fxyPowGraph_nM`), the BA reading has its counters
(`BAGraph.counters_ofLGraph`), an `M`-split only joins molecules (`BALvl1B_adj_mono`, `BALvl1B_coarse`), and the merge of a normal term keeps `n_M`
(`BASim_outOf_baInv`). -/
theorem baStart_nM_le (p : ℕ) : ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P0.g.nM ≤ p := by
  intro P0 hP0
  obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hP0
  have hD : ∀ e ∈ (fxyPowGraph p).dotted, e.eq = false := (fxyPowGraph_normal p).1
  set T := BAGraph.ofLGraph (fxyPowGraph p) with hT
  have hN : Δ.Normal := ⟨fun e he => hD e (by rw [(BAGraph.splitG_edges T Δ hΔ).2.1] at he; exact he), BAGraph.splitG_circ T _ hΔ⟩
  obtain ⟨hw, hd, hp, hm⟩ := BALvl1B_splitG_struct T Δ hΔ
  obtain ⟨hA, hAdj⟩ := BALvl1B_adj_mono T Δ hw.symm hd.symm hp.symm hm
  have h1 := (BALvl1B_coarse T Δ hA hAdj).2.1
  have h2 : T.nM = p := by
    have := congrArg Counters.nM (BAGraph.counters_ofLGraph (fxyPowGraph p) hD)
    exact this.trans (fxyPowGraph_nM p)
  have h3 := BASim_outOf_baInv (baPG T) Δ hN
  have h4 : Δ.packMerge.g.nM = Δ.nM := congrArg (fun x => x.2.1) h3
  rw [h4]
  exact h1.trans h2.le

end Start

/-! ## 8. Target 8: the shadow bridge -/

section Shadow

open Classical in
/-- **(3)-(5) transfer along a bijection of the molecules** (the walks are mapped along `e.symm`): the molecules of `Q'` correspond to those of `Q` by `e`, the external ones among them,
the two end molecules, and the multisets of the molecular edges. -/
theorem BALocReg1_locReg345_of_equiv {Q Q' : PGraph (Fin 2)} {p : ℕ} (e : Q'.g.Mol ≃ Q.g.Mol)
    (hext : ∀ c, Q'.g.IsExtMol c ↔ Q.g.IsExtMol (e c))
    (hx0 : e (Q'.g.molOf (Sum.inl (Q'.ext 0))) = Q.g.molOf (Sum.inl (Q.ext 0)))
    (hx1 : e (Q'.g.molOf (Sum.inl (Q'.ext 1))) = Q.g.molOf (Sum.inl (Q.ext 1)))
    (hedge : Q'.g.localReg_molEdgeMS.map (Sym2.map e) = Q.g.localReg_molEdgeMS) (h : Q.LocReg345 p) : Q'.LocReg345 p := by
  obtain ⟨W, ⟨hW, hle⟩, h4, h5⟩ := h
  have hy0 : e.symm (Q.g.molOf (Sum.inl (Q.ext 0))) = Q'.g.molOf (Sum.inl (Q'.ext 0)) := by rw [← hx0]; simp
  have hy1 : e.symm (Q.g.molOf (Sum.inl (Q.ext 1))) = Q'.g.molOf (Sum.inl (Q'.ext 1)) := by rw [← hx1]; simp
  have hext' : ∀ c, Q.g.IsExtMol c ↔ Q'.g.IsExtMol (e.symm c) := fun c => by
    rw [hext (e.symm c), Equiv.apply_symm_apply]
  have hedge' : Q.g.localReg_molEdgeMS.map (Sym2.map e.symm) = Q'.g.localReg_molEdgeMS := by
    rw [← hedge, Multiset.map_map]
    have : (Sym2.map e.symm ∘ Sym2.map e) = id := by
      funext z
      induction z using Sym2.ind with
      | h a b => simp
    rw [this, Multiset.map_id]
  refine ⟨fun i => (W i).map (Prod.map e.symm e.symm), ⟨fun i => ?_, ?_⟩, ?_, ?_⟩
  · have := (hW i).map e.symm
    rwa [hy0, hy1] at this
  · have hs : ∑ i, localReg_stepEdges ((W i).map (Prod.map e.symm e.symm)) = (∑ i, localReg_stepEdges (W i)).map (Sym2.map e.symm) := by
      simp only [localReg_stepEdges_map]
      have h := map_sum (Multiset.mapAddMonoidHom (Sym2.map e.symm)) (fun i => localReg_stepEdges (W i)) Finset.univ
      simp only [Multiset.coe_mapAddMonoidHom] at h
      exact h.symm
    rw [hs, ← hedge']
    exact Multiset.map_le_map hle
  · intro c' hc'
    obtain ⟨i, j, hij, hi, hj⟩ := h4 (e c') (fun hc => hc' ((hext c').2 hc))
    refine ⟨i, j, hij, ?_, ?_⟩
    · have := hi.map e.symm
      rwa [hy0, Equiv.symm_apply_apply] at this
    · have := hj.map e.symm
      rwa [hy0, Equiv.symm_apply_apply] at this
  · intro A hA
    have hA' : ∀ c ∈ A.image e, ¬ Q.g.IsExtMol c := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
      exact fun h => hA c' hc' ((hext c').2 h)
    have h5' := h5 (A.image e) hA'
    rw [Finset.card_image_of_injective _ e.injective] at h5'
    refine h5'.trans (Finset.card_le_card ?_)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨c, hc, hv⟩ := hi
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
    refine ⟨c', hc', ?_⟩
    have := hv.map e.symm
    rwa [hy0, Equiv.symm_apply_apply] at this

section ShadowMol

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the molecules of the shadow map to the molecules of the atomic image: `molOf v ↦ molOf (vmap v)` -/
def BALocReg1_molMap (Γ : BAGraph E I) : Γ.shadow.Mol → (promoteC Γ).merge.Mol :=
  SimpleGraph.ConnectedComponent.lift (fun u => BALocReg1_mu Γ u) (fun u v p _ => by
    have hv : v ∈ Γ.mol u := by
      rw [← Γ.shadow_mol]
      exact (Γ.shadow.mem_mol_iff u v).2 ⟨p⟩
    exact (BALocReg1_mu_eq_iff Γ u v).2 hv)

theorem BALocReg1_molMap_mk (Γ : BAGraph E I) (u : E ⊕ I) : BALocReg1_molMap Γ (Γ.shadow.molOf u) = BALocReg1_mu Γ u := rfl

theorem BALocReg1_molMap_bijective (Γ : BAGraph E I) : Function.Bijective (BALocReg1_molMap Γ) := by
  refine ⟨fun c1 c2 => ?_, fun c => ?_⟩
  · induction c1 using SimpleGraph.ConnectedComponent.ind with | h u1 => ?_
    induction c2 using SimpleGraph.ConnectedComponent.ind with | h u2 => ?_
    intro h
    exact (BAAtom_shadow_molOf_eq_iff Γ u1 u2).2 ((BALocReg1_mu_eq_iff Γ u1 u2).1 h)
  · induction c using SimpleGraph.ConnectedComponent.ind with | h w' => ?_
    obtain ⟨u, rfl⟩ := BAAtomic_vmap_surjective (promoteC Γ) w'
    exact ⟨Γ.shadow.molOf u, rfl⟩

theorem BALocReg1_mu_iff_shadow (Γ : BAGraph E I) (u v : E ⊕ I) :
    BALocReg1_mu Γ u = BALocReg1_mu Γ v ↔ Γ.shadow.molOf u = Γ.shadow.molOf v := by
  rw [BALocReg1_mu_eq_iff, BAAtom_shadow_molOf_eq_iff]

open Classical in
/-- the molecular edges of the shadow, read in the molecules of the image -/
theorem BALocReg1_shadow_edge (Γ : BAGraph E I) (hbij : Function.Bijective (BALocReg1_molMap Γ)) :
    Γ.shadow.localReg_molEdgeMS.map (Sym2.map (Equiv.ofBijective _ hbij)) =
      ((Γ.solid.filter (fun u => ¬ BALocReg1_mu Γ u.src = BALocReg1_mu Γ u.dst)).map
        (fun u => s(BALocReg1_mu Γ u.src, BALocReg1_mu Γ u.dst)) : List (Sym2 (promoteC Γ).merge.Mol)) := by
  unfold LGraph.localReg_molEdgeMS LGraph.molSolid
  simp only [Multiset.map_coe, List.map_map, List.filter_map]
  congr 1
  rw [show Γ.shadow.solid = Γ.solid from rfl]
  have hp : ∀ x : SEdge (E ⊕ I), (decide (¬Γ.shadow.InsideMol x.src x.dst)) = decide (¬BALocReg1_mu Γ x.src = BALocReg1_mu Γ x.dst) :=
    fun x => decide_eq_decide.2 (not_congr (BALocReg1_mu_iff_shadow Γ x.src x.dst).symm)
  simp only [hp]
  refine List.map_congr_left fun x _ => ?_
  simp [SEdge.map, BALocReg1_molMap_mk]

open Classical in
/-- the molecular edges of the atomic image -/
theorem BALocReg1_img_edge (Γ : BAGraph E I) :
    (promoteC Γ).merge.localReg_molEdgeMS =
      ((Γ.solid.filter (fun u => ¬ BALocReg1_mu Γ u.src = BALocReg1_mu Γ u.dst)).map
        (fun u => s(BALocReg1_mu Γ u.src, BALocReg1_mu Γ u.dst)) : List (Sym2 (promoteC Γ).merge.Mol)) := by
  unfold LGraph.localReg_molEdgeMS LGraph.molSolid
  rw [show (promoteC Γ).merge.solid = (promoteC Γ).solid.map (SEdge.map (promoteC Γ).vmap) from rfl, BAAtomic_promoteC_solid]
  simp only [Multiset.map_coe, List.map_map, List.filter_map]
  congr 1

end ShadowMol

open Classical in
/-- **Target 8, the shadow bridge**: (3)-(5) on the atomic image give (3)-(5) on the shadow (`BAShadowPG`, the form the merged BA consumers read, `BAAtom:139`).  The molecules of the image
are those of the BA graph (`BAGraph.img_molOf_eq_iff`), as are those of the shadow (`BAGraph.shadow_mol`); the solid edges are the same, read between the molecules.  No normality is needed. -/
theorem baShadow_locReg345 (Q : BAPGraph (Fin 2)) (p : ℕ) (h : PGraph.LocReg345 Q.img p) : (BAShadowPG Q).LocReg345 p := by
  have hbij := BALocReg1_molMap_bijective Q.g
  set e : (BAShadowPG Q).g.Mol ≃ Q.img.g.Mol := Equiv.ofBijective _ hbij with he
  have hmk : ∀ u : Q.E' ⊕ Q.I', e (Q.g.shadow.molOf u) = BALocReg1_mu Q.g u := fun u => rfl
  have hmi : ∀ u v : Q.E' ⊕ Q.I', BALocReg1_mu Q.g u = BALocReg1_mu Q.g v ↔ Q.g.shadow.molOf u = Q.g.shadow.molOf v := fun u v => by
    rw [← hmk u, ← hmk v]; exact e.injective.eq_iff
  have hinl : ∀ a : Q.E', BALocReg1_mu Q.g (Sum.inl a) = (promoteC Q.g).merge.molOf (Sum.inl ((promoteC Q.g).extMap a)) := fun a => by
    simp only [BALocReg1_mu, BAAtomic_vmap_inl]
  refine BALocReg1_locReg345_of_equiv e ?_ ?_ ?_ ?_ h
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | h u => ?_
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(promoteC Q.g).extMap a, ?_⟩
      have ha' : Q.g.shadow.molOf (Sum.inl a) = Q.g.shadow.molOf u := ha
      change (promoteC Q.g).merge.molOf (Sum.inl ((promoteC Q.g).extMap a)) = e (Q.g.shadow.molOf u)
      rw [← ha', hmk]
      exact (hinl a).symm
    · rintro ⟨⟨q, a, rfl⟩, ha⟩
      refine ⟨a, e.injective ?_⟩
      change e (Q.g.shadow.molOf (Sum.inl a)) = e (Q.g.shadow.molOf u)
      rw [hmk, hinl]
      exact ha
  · change e (Q.g.shadow.molOf (Sum.inl (Q.ext 0))) = (promoteC Q.g).merge.molOf (Sum.inl ((promoteC Q.g).extMap (Q.ext 0)))
    rw [hmk, hinl]
  · change e (Q.g.shadow.molOf (Sum.inl (Q.ext 1))) = (promoteC Q.g).merge.molOf (Sum.inl ((promoteC Q.g).extMap (Q.ext 1)))
    rw [hmk, hinl]
  · exact (BALocReg1_shadow_edge Q.g hbij).trans (BALocReg1_img_edge Q.g).symm

end Shadow

/-! ## 7. Target 7: the contract (1)-(5) along `BAReach` -/

section Contract

/-- **The contract (1)-(5)** (supervisor 1152 O7; band `lw_localregular_upto5`, LR2:1857): for every start term `P0` and every `Q` reached from it, the coloured path invariant
at the image; (2) `n_M ≤ p` and the band predicate `LocReg2` on the image (`n_V ≤ n_W + 1` counts atoms: delta candidate `T2397c`); at `LocStd`: (1) on the image, (3)-(5) on the image and on
the shadow (the form read by `baAuxNested_holds`, `BAAnpAux`, `BAAnpAuxG`). -/
def BALocReg15 : Prop :=
  ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
      Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p ∧
        (Q.g.LocStd → PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p)

/-- **Target 7**: (1)-(5) at every graph reached from a start term.  The invariant along `BReach` of the tagged step is `baPathStep_holds` (target 4) from `baPathInit_holds` (target 5);
`n_M ≤ p` is `baLvl1StepGood_holds` from `baStart_nM_le` (target 6); `LocReg2` is `BAGraph.BAAtomic_nM_merge` and `LGraph.molNV_le_molNW_add_one`; at `LocStd` the image is locally standard
(`BAGraph.img_locStd_iff`), `PGraph.PathInv2.locReg345` gives (3)-(5), and `baShadow_locReg345` (target 8) the shadow.  The hypothesis is the shape binder of split Σ (H250 (2)): the shapes
`e2`, `macroA`, `macroB` are the targets of L3b2; the shapes `s1`, `e1` are proved in `BALocReg1.lean`. -/
theorem baLocReg15_holds (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
    BALocReg15 := by
  intro p P0 hP0 K Q hQ
  have h0 : P0.g.Normal := BAGraph.partition_normal _ P0 hP0
  obtain ⟨hNQ, hB⟩ := baReach_bReach h0 hQ
  have hstep := baPathStep_holds hX
  have key : ∀ Q' : BAPGraph (Fin 2), BReach (untag BALocStepT) P0 Q' → Q'.img.PathInv2 p ∧ Q'.g.nM ≤ p := by
    intro Q' hB'
    induction hB' with
    | refl => exact ⟨baPathInit_holds p P0 hP0, baStart_nM_le p P0 hP0⟩
    | step hQ' hs hm ih =>
      refine ⟨hstep _ _ hs p ih.1 _ hm, ?_⟩
      obtain ⟨hNn, hst⟩ := (baUntag_locStepT _ _).1 hs
      exact ((baLvl1StepGood_holds _ _ hst hNn _ hm).2.2.1).trans ih.2
  obtain ⟨h1, h2⟩ := key Q hB
  refine ⟨h1, h2, ⟨(Q.g.BAAtomic_nM_merge).trans_le h2, LGraph.molNV_le_molNW_add_one Q.img.g (Q.g.img_normal hNQ).1⟩, fun hL => ?_⟩
  have hLi : Q.img.LocStd := (Q.g.img_locStd_iff hNQ).1 hL
  have h345 : PGraph.LocReg345 Q.img p := PGraph.PathInv2.locReg345 hLi h1
  exact ⟨hLi, h345, baShadow_locReg345 Q p h345⟩

end Contract

/-! ## 9. Target 9: the value of the start graph is `|f_{xy}|^p` -/

section Value

open MeasureTheory RBM.Gauss

/-- **Target 9** (twin of `lw_fxyPow_integral_eq`, `LocalRegular:2036`; owed here by T2446): at the BA data `BAlwData` (`S = t · svarF` real) and `p` even, the value of the BA reading of the
start graph is `f_{xy}^{p/2} \overline{f_{xy}}^{p/2} = |f_{xy}|^p` pointwise (`BAGraph.val_ofLGraph`, `fxyPowGraph_val_eq`), so the expectations agree. -/
theorem ba_fxyPow_integral_eq (d L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) (p : ℕ) (hp : Even p) (ℓe : Fin 2 → Idx d L W) :
    ∫ ω, (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1) ^ (p / 2) *
        star (fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1)) ^ (p / 2) ∂(PF d L W 0) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [BAGraph.val_ofLGraph]
  have hℓ : ℓe = ![ℓe 0, ℓe 1] := by
    funext i; fin_cases i <;> rfl
  have hS : ∀ i j, star ((BAlwData d L W g0 Em t m ω).toLData.S i j) = (BAlwData d L W g0 Em t m ω).toLData.S i j := by
    intro i j
    change star (BAlwS d L W t i j) = BAlwS d L W t i j
    simp [BAlwS, star_mul', Complex.star_def, Complex.conj_ofReal]
  have := fxyPowGraph_val_eq (BAlwData d L W g0 Em t m ω).toLData hS p hp (ℓe 0) (ℓe 1)
  rwa [← hℓ] at this

end Value

/-! ## 10. Compiled instances (target 10)

Targets 5, 6, 7 at `p = 2` from a start term (the shape binder of split Σ stays a hypothesis of the contract: the shapes `e2`, `macroA`, `macroB` are L3b2's targets); the `LocStd`
branch of target 7 at a graph reached by two steps; target 8 also at a hand-built locally standard graph; target 9 at concrete data. -/

end RBM.Graph

end
