/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BAScost
import RBM3D.Graph.BAScost2
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BASymm2
import RBM3D.Graph.LocalRegular
import RBM3D.Graph.LocalRegular6a
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LWSymm

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
# Property (6) at BA: the tagged step, `BASimC'`, `BABridge`, `BAFinalS`, the assembly

Paper: Lemma B.6 (`lanlw`), Lemma B.7 (`lem_lweight`), (B.20) `GGGamma`, the BA step (Definition
7.14 `deflvl1`); property (6) of Lemma 7.17 (`lem:localregular`).  The step lemma of `BAStep` comes
from the band step `locCostGe_locStep` (`Graph/LocalRegular6d.lean`) at the `band` outputs,
through a simulation up to relabelling (`BASimC'`), and from the shape lemmas of
`Graph/BAScost.lean` at the other outputs; the final step reads atom-level `LocStd`.

## Contents (namespace `RBM.Graph`; private prefix `BAStepS_`)

1. **The statements**: `BAFrameStepTN`, `BALocStepT` (tagged steps, `def`s over the non-recursive
   `BAFrameStepT`), `BABridge`, `BAEquivCost`, `BACostTwist`, `BASimC'`, `BAFinalS`, `BALocReg6`.
2. `baUntag_locStepT` (`untag BALocStepT P L ↔ P.g.Normal ∧ BALocStep P L`), `baNormal_locStepT`
   (no frame-normality hypothesis: every output of a `BAFrameStepT` constructor is an element of a
   partition, `BAGraph.partition_normal`), the lemmas `baUntag_locStepT_intro`,
   `baInit_locReg6InvA`.
3. `baBridge_holds`, `baEquivCost_holds`, `baCostTwist_holds`, `baShapeLL_twist`.
4. `baSimC'_holds` (`P' := (P.twist c t).img`, `baMatch_holds` per `band` output).
5. `baStep_of_simC'`; the shapes `s1` (vacuous) and `e1` (`baShapeLL_e1`) of `BAFrameStepTN`:
   `baShapeLL_s1_tn`, `baShapeLL_e1_tn`.
6. `baFinalS_holds` (through `P.img`).
7. `ba_ord_ge_of_simC'` along `BReach`, `baReach_bReach`, the closed form `baLocReg6_reach` along
   `BAReach`.

Combinatorial; no data; `m` occurs only as the label of `LocStep`.  The
twist is not matched step by step: `P' := (P.twist c t).img`, and the twist moves into the costs
(`baCostTwist_holds`).  The shapes `e2`, `macroA`, `macroB` of `BAFrameStepTN` are hypotheses of
`BALocReg6`; they are proved in `Graph/BAShapeO2B.lean`.
-/

noncomputable section

namespace RBM.Graph

/-! ## 1. The statements -/

/-- **The tagged frame step with normality**: a normal `P` and a `BAFrameStepT` at `P`. -/
def BAFrameStepTN : BTStep := fun P LT => P.g.Normal ∧ BAFrameStepT P LT

/-- **The tagged BA step**: at a normal `P`, a `BAFrameStepT` at `P.twist c t`, every output twisted back, the tags kept. -/
def BALocStepT : BTStep := fun P LT =>
  P.g.Normal ∧ ∃ (c t : Bool) (LT0 : List (BAShape × BAPGraph (Fin 2))),
    BAFrameStepT (P.twist c t) LT0 ∧ LT = LT0.map (fun x => (x.1, BAPGraph.twist c t x.2))

/-- **`BABridge`**: the cost at atoms of `P` is the band cost of the atomic image `P.img`. -/
def BABridge : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k P ↔ PGraph.LocCostGe far k P.img

/-- the cost transfers along `BAEquivC` -/
def BAEquivCost : Prop :=
  ∀ (R S : PGraph (Fin 2)), R.BAEquivC S → ∀ (far : Bool) (k : ℤ), (R.LocCostGe far k ↔ S.LocCostGe far k)

/-- the twist leaves the cost at atoms invariant -/
def BACostTwist : Prop :=
  ∀ (c t : Bool) (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k (P.twist c t) ↔ locCostGeA far k P

/-- **`BASimC'`**: the band step is chosen per output, `P'` per step. -/
def BASimC' (m : ℂ) (T : BTStep) : Prop :=
  ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), P'.g.Normal ∧ LGraph.CircIffLoop P'.g ∧
    (∀ far k, locCostGeA far k P → P'.LocCostGe far k) ∧
      ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L',
        ∀ far k, R.LocCostGe far k → locCostGeA far k Q

/-- **`BAFinalS`**: the final step: at a graph `P` of `R` with atom-level `P.g.LocStd`, (6) holds (the order bounds the cost, for `Φ^all` and, for atoms of `x`, `y` apart, `Φ^far`). -/
def BAFinalS (R : BAPGraph (Fin 2) → Prop) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (k : ℤ), R P → P.g.LocStd →
    (locCostGeA false k P → k ≤ P.scalingOrder) ∧
      (¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → locCostGeA true k P → k ≤ P.scalingOrder)

/-- **The closed form**: (6) at every graph that `BAReach` reaches from a start term (without the frame-normality hypothesis: `baNormal_locStepT` is unconditional).  The hypotheses are the shape inputs (`e2`, `macroA`, `macroB`); they are proved in `Graph/BAShapeO2B.lean`. -/
def BALocReg6 : Prop :=
  ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
    (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))

/-! ## 2. `untag`, normality (no frame-normality hypothesis is needed) -/

theorem baUntag_locStepT : ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))),
    untag BALocStepT P L ↔ P.g.Normal ∧ BALocStep P L := by
  intro P L
  constructor
  · rintro ⟨LT, ⟨hN, c, t, LT0, hF, rfl⟩, rfl⟩
    refine ⟨hN, c, t, LT0.map Prod.snd, (baFrameStepT_untag_holds _ _).2 ⟨LT0, hF, rfl⟩, ?_⟩
    simp [List.map_map, Function.comp_def]
  · rintro ⟨hN, c, t, F, hF, rfl⟩
    obtain ⟨LT0, hF0, rfl⟩ := (baFrameStepT_untag_holds _ _).1 hF
    exact ⟨LT0.map (fun x => (x.1, BAPGraph.twist c t x.2)), ⟨hN, c, t, LT0, hF0, rfl⟩, by simp [List.map_map, Function.comp_def]⟩

private theorem BAStepS_outsT_normal (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) : ∀ x ∈ P.outsT tg Ts, x.2.g.Normal := by
  rintro ⟨t, Q⟩ hx
  obtain ⟨T, -, T', hT', -, rfl⟩ := BASim_mem_outsT P tg Ts t Q hx
  exact BAGraph.partition_normal T T'.packMerge (List.mem_map.2 ⟨T', hT', rfl⟩)

private theorem BAStepS_frameT_normal {P : BAPGraph (Fin 2)} {LT : List (BAShape × BAPGraph (Fin 2))} (h : BAFrameStepT P LT) :
    ∀ x ∈ LT, x.2.g.Normal := by
  cases h <;> simp only [BAPGraph.withinOutsT, BAPGraph.splitOutsT, List.forall_mem_append] <;> (repeat' constructor) <;>
    exact BAStepS_outsT_normal _ _ _

theorem baNormal_locStepT : BANormal (untag BALocStepT) := by
  rintro P L ⟨LT, ⟨hN, c, t, LT0, hF, rfl⟩, rfl⟩ Q hQ
  obtain ⟨⟨sh, Q0⟩, hmem, rfl⟩ := List.mem_map.1 hQ
  obtain ⟨⟨sh', Q1⟩, hmem1, he⟩ := List.mem_map.1 hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact (ba_twist_inv_out c t Q1.g).2.2.2.2.2 (BAStepS_frameT_normal hF _ hmem1)

/-- an `untag` introduction at `BALocStepT` (supplies the premise of `untag`) -/
theorem baUntag_locStepT_intro {P : BAPGraph (Fin 2)} {L : List (BAPGraph (Fin 2))} (hN : P.g.Normal) (h : BALocStep P L) :
    untag BALocStepT P L := (baUntag_locStepT P L).2 ⟨hN, h⟩

/-- `locReg6InvA` at the start terms (`baInit_holds`) -/
theorem baInit_locReg6InvA {p : ℕ} {P0 : BAPGraph (Fin 2)} (h : P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition) : locReg6InvA p P0 :=
  baInit_holds p P0 h

/-! ## 3. The bridge, the relabelling and the twist leave the cost invariant -/

private theorem BAStepS_scost_img {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (s' : Setoid ((promoteC Γ).ExtCls ⊕ (promoteC Γ).IntCls)) :
    (promoteC Γ).merge.scost s' = scostA Γ (Setoid.comap (promoteC Γ).vmap s') := by
  unfold scostA
  rw [← LGraph.scost_relabel (promoteC Γ) (promoteC Γ).extMap (promoteC Γ).extMap_surj (promoteC Γ).vmap
    (BAAtomic_vmap_surjective _) (BAAtomic_vmap_inl _) s']
  exact localReg6a_scost_congr _ _ s' rfl rfl

private theorem BAStepS_vmap_atom {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) {u v : E ⊕ I} :
    (promoteC Γ).vmap u = (promoteC Γ).vmap v ↔ atomSetoid Γ u v :=
  (BAAtomic_promoteC_vmap_eq_atom Γ u v).trans (BAAtomic_atomSetoid_iff Γ u v).symm

/-- **`baBridge_holds`**: the classes of `promoteC` are the atoms (`Graph/BAAtomic.lean`); `LGraph.scost_relabel` (`Graph/LocalRegular6a.lean`) along the class map `vmap`; the far clause through
`vmap (inl a) = inl (extMap a)`. -/
theorem baBridge_holds : BABridge := by
  intro P far k
  constructor
  · intro hk s' hfar
    refine le_of_le_of_eq (hk (Setoid.comap (promoteC P.g).vmap s') (fun u v h => ?_) (fun hf hxy => hfar hf ?_))
      (BAStepS_scost_img P.g s').symm
    · have h' : s' ((promoteC P.g).vmap u) ((promoteC P.g).vmap v) := by rw [(BAStepS_vmap_atom P.g).2 h]; exact s'.refl' _
      exact h'
    · have h' : s' ((promoteC P.g).vmap (Sum.inl (P.ext 0))) ((promoteC P.g).vmap (Sum.inl (P.ext 1))) := hxy
      rwa [BAAtomic_vmap_inl, BAAtomic_vmap_inl] at h'
  · intro hk s hs hfar
    set g := Function.surjInv (BAAtomic_vmap_surjective (promoteC P.g)) with hg
    have hvg : ∀ w, (promoteC P.g).vmap (g w) = w := Function.surjInv_eq (BAAtomic_vmap_surjective (promoteC P.g))
    have hcomap : Setoid.comap (promoteC P.g).vmap (Setoid.comap g s) = s := by
      ext u v
      have hu : s u (g ((promoteC P.g).vmap u)) := hs ((BAStepS_vmap_atom P.g).1 (hvg _).symm)
      have hv : s v (g ((promoteC P.g).vmap v)) := hs ((BAStepS_vmap_atom P.g).1 (hvg _).symm)
      change s (g ((promoteC P.g).vmap u)) (g ((promoteC P.g).vmap v)) ↔ s u v
      exact ⟨fun h => s.trans (s.trans hu h) (s.symm hv), fun h => s.trans (s.trans (s.symm hu) h) hv⟩
    refine le_of_le_of_eq (hk (Setoid.comap g s) (fun hf hxy => hfar hf ?_)) ((BAStepS_scost_img P.g (Setoid.comap g s)).trans (by rw [hcomap]))
    rw [← hcomap]
    change (Setoid.comap g s) ((promoteC P.g).vmap (Sum.inl (P.ext 0))) ((promoteC P.g).vmap (Sum.inl (P.ext 1)))
    rw [BAAtomic_vmap_inl, BAAtomic_vmap_inl]
    exact hxy

/-- the transfer along the relation `BAEquivC`: `scost_relabel` along `Sum.map eE eI`, then `LGraph.scost_perm` (`Graph/LocalRegular6a.lean`) -/
theorem baEquivCost_holds : BAEquivCost := by
  rintro R S ⟨eE, eI, hext, hsol, ⟨l, hl, hF⟩, -, -⟩ far k
  have hW : (R.g.relabel (Sum.map eE eI)).waved.length = S.g.waved.length := hl.length_eq.symm.trans hF.length_eq
  have hcost : ∀ s : Setoid (S.E' ⊕ S.I'), S.g.scost s = R.g.scost (Setoid.comap (Sum.map eE eI) s) := fun s =>
    (LGraph.scost_perm _ _ hsol hW s).symm.trans
      (LGraph.scost_relabel R.g eE eE.surjective (Sum.map eE eI) (Sum.map_surjective.2 ⟨eE.surjective, eI.surjective⟩) (fun _ => rfl) s)
  have hfar : ∀ s : Setoid (S.E' ⊕ S.I'), Setoid.comap (Sum.map eE eI) s (Sum.inl (R.ext 0)) (Sum.inl (R.ext 1)) ↔
      s (Sum.inl (S.ext 0)) (Sum.inl (S.ext 1)) := fun s => by
    change s (Sum.inl (eE (R.ext 0))) (Sum.inl (eE (R.ext 1))) ↔ _
    rw [hext, hext]
  constructor
  · intro h s hs
    rw [hcost]
    exact h _ (fun hf hxy => hs hf ((hfar s).1 hxy))
  · intro h s hs
    have hrt : ∀ u : R.E' ⊕ R.I', Sum.map eE.symm eI.symm (Sum.map eE eI u) = u := fun u => by cases u <;> simp
    have hcs : Setoid.comap (Sum.map eE eI) (Setoid.comap (Sum.map eE.symm eI.symm) s) = s := by
      ext u v
      change s (Sum.map eE.symm eI.symm (Sum.map eE eI u)) (Sum.map eE.symm eI.symm (Sum.map eE eI v)) ↔ s u v
      rw [hrt, hrt]
    have := h (Setoid.comap (Sum.map eE.symm eI.symm) s) (fun hf hxy => hs hf (by rw [← hcs]; exact (hfar _).2 hxy))
    rw [hcost, hcs] at this
    exact this

private theorem BAStepS_scostA_twist {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : BAGraph E I)
    (s : Setoid (E ⊕ I)) : scostA (Γ.twist c t) s = scostA Γ s := by
  have hsol : (promoteC (Γ.twist c t)).solid = (lwSymmTwistG c t (promoteC Γ)).solid := by
    rw [lwSymmTwistG_solid, BAAtomic_promoteC_solid, BAAtomic_promoteC_solid, List.map_map,
      show (Γ.twist c t).solid = Γ.solid.map (lwSymmTwistS c t) from lwSymmTwistG_solid c t Γ.toLGraph, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply, BAGraph.BASymm1_twist_sameAtom]
    cases c <;> cases t <;> simp [lwSymmTwistS, SEdge.conj, SEdge.transpose, Γ.BAAtomic_sameAtom_comm]
  have hw : (promoteC (Γ.twist c t)).waved.length = (lwSymmTwistG c t (promoteC Γ)).waved.length := by
    cases c <;> cases t <;> simp [promoteC, lwSymmTwistG, LGraph.conj, LGraph.transpose, BAGraph.twist]
  unfold scostA
  rw [← LGraph.scost_twist c t (promoteC Γ) s]
  exact localReg6a_scost_congr _ _ s (by simp only [LGraph.skept, hsol]) hw

/-- **The twist leaves `locCostGeA` invariant** (`LGraph.scost_twist` in `Graph/LocalRegular6d.lean`, `BAGraph.BASymm1_twist_atom` in `Graph/BASymm1.lean`) -/
theorem baCostTwist_holds : BACostTwist := by
  intro c t P far k
  have hat : atomSetoid (P.g.twist c t) = atomSetoid P.g := by simp only [atomSetoid, BAGraph.BASymm1_twist_atom]
  exact ⟨fun h s hs hfar => le_of_le_of_eq (h s (hat ▸ hs) hfar) (BAStepS_scostA_twist c t P.g s),
    fun h s hs hfar => le_of_le_of_eq (h s (hat ▸ hs) hfar) (BAStepS_scostA_twist c t P.g s).symm⟩

/-- the shape lemma of a frame step carries to the twisted step -/
theorem baShapeLL_twist : ∀ sh : BAShape, BAShapeLL sh BAFrameStepTN → BAShapeLL sh BALocStepT := by
  intro sh h P LT ⟨hN, c, t, LT0, hF, hLT⟩ Q hQ far k hk
  subst hLT
  obtain ⟨⟨sh', Q0⟩, hmem, he⟩ := List.mem_map.1 hQ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact (baCostTwist_holds c t Q0 far k).2 (h (P.twist c t) LT0 ⟨(ba_twist_inv_out c t P.g).2.2.2.2.2 hN, hF⟩ Q0 hmem far k
    ((baCostTwist_holds c t P far k).2 hk))

/-! ## 4. `BASimC'` at the tagged step, `P' := (P.twist c t).img` -/

/-- Take `P' := (P.twist c t).img` (normal and `CircIffLoop`: `ba_twist_inv_out`, `BAGraph.img_normal`); for each `band` output, `baMatch_holds` at `P.twist c t`;
the costs move by `baEquivCost_holds` and `baCostTwist_holds`. -/
theorem baSimC'_holds (m : ℂ) : BASimC' m BALocStepT := by
  rintro P LT ⟨hN, c, t, LT0, hF, rfl⟩
  have hN2 : (P.twist c t).g.Normal := (ba_twist_inv_out c t P.g).2.2.2.2.2 hN
  refine ⟨(P.twist c t).img, ((P.twist c t).g.img_normal hN2).1, ((P.twist c t).g.img_normal hN2).2,
    fun far k hk => (baBridge_holds _ far k).1 ((baCostTwist_holds c t P far k).2 hk), fun Q hQ => ?_⟩
  obtain ⟨⟨sh, Q0⟩, hmem, he⟩ := List.mem_map.1 hQ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨L', hst, R, hR, hRE⟩ := baMatch_holds m (P.twist c t) LT0 hF hN2 Q0 hmem
  exact ⟨L', hst, R, hR, fun far k hRk => (baCostTwist_holds c t Q0 far k).2 ((baBridge_holds Q0 far k).2
    ((baEquivCost_holds R Q0.img (PGraph.BASim_BAEquiv_toC hRE) far k).1 hRk))⟩

/-! ## 5. The step from the simulation (per output), and the closed shapes `s1`, `e1` -/

/-- **The step lemma from a simulation**: the `band` outputs by `locCostGe_locStep` (`Graph/LocalRegular6d.lean`) at the band step of `BASimC'`, the others by the shape lemmas. -/
theorem baStep_of_simC' : ∀ (m : ℂ) (T : BTStep), BASimC' m T → (∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) → BAStep (untag T) := by
  intro m T hS hX
  rintro P L ⟨LT, hT, rfl⟩ far k hk Q hQ
  obtain ⟨⟨sh, Q⟩, hmem, rfl⟩ := List.mem_map.1 hQ
  by_cases hb : sh = BAShape.band
  · subst hb
    obtain ⟨P', hN, hC, hc, hR⟩ := hS P LT hT
    obtain ⟨L', hst, R, hR', hRQ⟩ := hR Q hmem
    exact hRQ far k (locCostGe_locStep hst hN hC far k (hc far k hk) R hR')
  · exact hX sh hb P LT hT Q hmem far k hk

private theorem BAStepS_tagStd_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (k : ℕ)
    (T' : BAGraph E (I ⊕ Fin k)) : Γ.tagStd k T' ≠ BAShape.s1 ∧ Γ.tagStd k T' ≠ BAShape.e1 := by
  unfold BAGraph.tagStd
  split_ifs <;> simp

private theorem BAStepS_tagT1_ne {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (T' : BAGraph E (I ⊕ Fin 2)) : Γ.tagT1 T' ≠ BAShape.s1 := by
  unfold BAGraph.tagT1
  split_ifs <;> simp

/-- the outputs of `outsT` with a tag that is neither `s1` nor `e1` -/
private theorem BAStepS_outsT_ne (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (hs : ∀ T', tg T' ≠ BAShape.s1 ∧ tg T' ≠ BAShape.e1) :
    ∀ x ∈ P.outsT tg Ts, x.1 ≠ BAShape.s1 ∧ x.1 ≠ BAShape.e1 := by
  rintro ⟨t, Q⟩ hx
  obtain ⟨T, -, T', -, rfl, -⟩ := BASim_mem_outsT P tg Ts t Q hx
  exact hs T'

/-- an `e1` output of `outsT` is a packed term of the partition of an element of `Ts`; no output is tagged `s1` -/
private theorem BAStepS_outsT_pack (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (tg : BAGraph P.E' I' → BAShape)
    (Ts : List (BAGraph P.E' I')) (hs : ∀ T', tg T' ≠ BAShape.s1) :
    ∀ x ∈ P.outsT tg Ts, x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ T ∈ Ts, ∃ Q0 ∈ T.partition, x.2 = BAScost_pack P Q0) := by
  rintro ⟨t, Q⟩ hx
  obtain ⟨T, hT, T', hT', rfl, rfl⟩ := BASim_mem_outsT P tg Ts t Q hx
  exact ⟨hs T', fun _ => ⟨T, hT, T'.packMerge, List.mem_map.2 ⟨T', hT', rfl⟩, rfl⟩⟩

/-- the tags of the outputs of a `BAFrameStepT`: none is `s1`; an `e1` output is a packed term of `lanlwT1 P.g p` at a blue circled edge `p` -/
private theorem BAStepS_frameT_tags {P : BAPGraph (Fin 2)} {LT : List (BAShape × BAPGraph (Fin 2))} (h : BAFrameStepT P LT) :
    ∀ x ∈ LT, x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
      ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := by
  have hstd : ∀ (k : ℕ) (Ts : List (BAGraph P.E' (P.I' ⊕ Fin k))) (x : BAShape × BAPGraph (Fin 2)), x ∈ P.outsT (P.g.tagStd k) Ts →
      x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
        ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := fun k Ts x hx =>
    ⟨(BAStepS_outsT_ne P _ Ts (BAStepS_tagStd_ne P.g k) x hx).1, fun h1 => absurd h1 (BAStepS_outsT_ne P _ Ts (BAStepS_tagStd_ne P.g k) x hx).2⟩
  have hconst : ∀ (sh : BAShape), sh ≠ BAShape.s1 → sh ≠ BAShape.e1 → ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I'))
      (x : BAShape × BAPGraph (Fin 2)), x ∈ P.outsT (fun _ => sh) Ts →
      x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
        ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := fun sh h1 h2 {I'} _ _ Ts x hx =>
    ⟨(BAStepS_outsT_ne P _ Ts (fun _ => ⟨h1, h2⟩) x hx).1, fun h3 => absurd h3 (BAStepS_outsT_ne P _ Ts (fun _ => ⟨h1, h2⟩) x hx).2⟩
  have ht1 : ∀ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) → ∀ (x : BAShape × BAPGraph (Fin 2)),
      x ∈ P.outsT P.g.tagT1 [BAGraph.lanlwT1 P.g p] → x.1 ≠ BAShape.s1 ∧ (x.1 = BAShape.e1 → ∃ p ∈ lwSplit P.g.solid, (p.1.σ = true ∧ p.1.circ = true) ∧
        ∃ Q0 ∈ (BAGraph.lanlwT1 P.g p).partition, x.2 = BAScost_pack P Q0) := by
    intro p hp hp1 x hx
    obtain ⟨h1, h2⟩ := BAStepS_outsT_pack P _ _ (BAStepS_tagT1_ne P.g) x hx
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

/-- **`BAShapeLL s1 BAFrameStepTN` is vacuous**: no constructor of `BAFrameStepT` tags an output `s1` (`tagStd`: `e2`/`band`; `tagT1`: `e1`/`band`; the rest are constants). -/
theorem baShapeLL_s1_tn : BAShapeLL BAShape.s1 BAFrameStepTN := by
  rintro P LT ⟨-, hF⟩ Q hQ
  exact absurd rfl (BAStepS_frameT_tags hF _ hQ).1

/-- **`BAShapeLL e1 BAFrameStepTN`** follows from `baShapeLL_e1` (`Graph/BAScost2.lean`): the `e1` outputs of `edge` and `ggSplit` are the `tagT1` outputs of `lanlwT1`, packed by `outsT`. -/
theorem baShapeLL_e1_tn : BAShapeLL BAShape.e1 BAFrameStepTN := by
  refine baShapeLL_e1 ?_
  rintro P LT ⟨-, hF⟩ Q hQ
  exact (BAStepS_frameT_tags hF _ hQ).2 rfl

/-! ## 6. `BAFinalS` at `LocStd`, through `P.img` -/

/-- At `P.g.LocStd` the atomic image `P.img` is locally standard (`BAGraph.img_locStd_iff`, `Graph/BAAtomic.lean`) with the same `scalingOrder`
(`BAImgCounters_holds`); the cost transfers by `baBridge_holds`; `locReg6_of_locCostGe` and `locReg6far_of_locCostGe` (`Graph/LocalRegular6a.lean`) close; the far clause needs
the fact that distinct external atoms give distinct externals of `P.img` (`hext`, from `BAAtomic_vmap_inl`). -/
theorem baFinalS_holds (R : BAPGraph (Fin 2) → Prop) : BAFinalS R := by
  intro P k _ hL
  have hstd : P.img.LocStd := (P.g.img_locStd_iff hL.1).1 hL
  have hord : P.img.g.scalingOrder = P.scalingOrder := by
    change ord _ = ord _
    rw [BAImgCounters_holds P]
    rfl
  have hext : ¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → P.img.ext 0 ≠ P.img.ext 1 := by
    intro hx heq
    apply hx
    have h1 : (promoteC P.g).vmap (Sum.inl (P.ext 0)) = (promoteC P.g).vmap (Sum.inl (P.ext 1)) := by
      rw [BAAtomic_vmap_inl, BAAtomic_vmap_inl]
      exact congrArg Sum.inl heq
    exact (BAStepS_vmap_atom P.g).1 h1
  refine ⟨fun hk => ?_, fun hx hk => ?_⟩
  · rw [← hord]; exact locReg6_of_locCostGe hstd ((baBridge_holds P false k).1 hk)
  · rw [← hord]; exact locReg6far_of_locCostGe hstd (hext hx) ((baBridge_holds P true k).1 hk)

/-! ## 7. The assembly along `BReach`, and the closed form along `BAReach` -/

/-- **The assembly**: (6) along `BReach` of the untagged step, from the step lemma `baStep_of_simC'`, normality, and `BAFinalS` at the reachable graphs. -/
theorem ba_ord_ge_of_simC' : ∀ (m : ℂ) (p : ℕ) (T : BTStep) (P0 : BAPGraph (Fin 2)), locReg6InvA p P0 → BANormal (untag T) → BASimC' m T →
    (∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) → BAFinalS (BReach (untag T) P0) → ∀ Q, BReach (untag T) P0 Q →
      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder)) := by
  intro m p T P0 h0 hN hS hX hF Q hQ
  have hStep := baStep_of_simC' m T hS hX
  have hinv : locReg6InvA p Q := by
    induction hQ with
    | refl => exact h0
    | step hQ' hst hmem ih =>
      exact ⟨hN _ _ hst _ hmem, hStep _ _ hst false _ ih.2.1 _ hmem, hStep _ _ hst true _ ih.2.2 _ hmem⟩
  exact ⟨hinv, fun hl => ⟨(hF Q _ hQ hl).1 hinv.2.1, fun hx => (hF Q _ hQ hl).2 hx hinv.2.2⟩⟩

/-- `BAReach` from a normal start term is `BReach` of the untagged tagged step, and normal along the way -/
theorem baReach_bReach {K : ℤ} {P0 Q : BAPGraph (Fin 2)} (h0 : P0.g.Normal) (h : BAReach K P0 Q) :
    Q.g.Normal ∧ BReach (untag BALocStepT) P0 Q := by
  induction h with
  | refl => exact ⟨h0, BReach.refl⟩
  | step Q' R L hPQ hlt hstd hls hR ih =>
    have hst : untag BALocStepT Q' L := (baUntag_locStepT Q' L).2 ⟨ih.1, hls⟩
    exact ⟨baNormal_locStepT Q' L hst R hR, BReach.step ih.2 hst hR⟩

/-- **The closed form**: (6) at every `Q` with `BAReach K P0 Q` from a start term `P0`.  The shapes `s1` and `e1` are closed here (`baShapeLL_s1_tn`, `baShapeLL_e1_tn`);
`e2`, `macroA`, `macroB` stay hypotheses (`BALocReg6` is conditional on them; they are proved in `Graph/BAShapeO2B.lean`). -/
theorem baLocReg6_reach : BALocReg6 := by
  intro p P0 hP0 hX K Q hQ
  have hX' : ∀ sh, sh ≠ BAShape.band → BAShapeLL sh BALocStepT := by
    intro sh hsh
    refine baShapeLL_twist sh ?_
    cases sh with
    | band => exact absurd rfl hsh
    | s1 => exact baShapeLL_s1_tn
    | e1 => exact baShapeLL_e1_tn
    | e2 => exact hX _ (Or.inl rfl)
    | macroA => exact hX _ (Or.inr (Or.inl rfl))
    | macroB => exact hX _ (Or.inr (Or.inr rfl))
  exact ba_ord_ge_of_simC' 0 p BALocStepT P0 (baInit_locReg6InvA hP0) baNormal_locStepT (baSimC'_holds 0) hX' (baFinalS_holds _) Q
    (baReach_bReach (BAGraph.partition_normal _ P0 hP0) hQ).2

end RBM.Graph

end
