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
import RBM3D.Test.Axioms

/-!
# T2443 probe (L3b4' `BAStepS'`, design gate; never merged)

The pins of targets 1-7 against `main` (check file `docs/tickets/checks/T2443-check.lean`; the statements are its `T2443_*` up to the name, except the
closed form `BALocReg6`: no frame-normality hypothesis).  Proved: targets 1-6, the assembly `ba_ord_ge_of_simC'` and the closed form
`baLocReg6_of_shapes` (shapes `s1`, `e1` as hypotheses).  `BAMatchTw` and its bridges are not used (1a (i)).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Graph

/-! ## The pins -/

def BAFrameStepTN : BTStep := fun P LT => P.g.Normal ∧ BAFrameStepT P LT

def BALocStepT : BTStep := fun P LT =>
  P.g.Normal ∧ ∃ (c t : Bool) (LT0 : List (BAShape × BAPGraph (Fin 2))),
    BAFrameStepT (P.twist c t) LT0 ∧ LT = LT0.map (fun x => (x.1, BAPGraph.twist c t x.2))

def BABridge : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k P ↔ PGraph.LocCostGe far k P.img

def BAEquivCost : Prop :=
  ∀ (R S : PGraph (Fin 2)), R.BAEquivC S → ∀ (far : Bool) (k : ℤ), (R.LocCostGe far k ↔ S.LocCostGe far k)

def BACostTwist : Prop :=
  ∀ (c t : Bool) (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k (P.twist c t) ↔ locCostGeA far k P

def BASimC' (m : ℂ) (T : BTStep) : Prop :=
  ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), P'.g.Normal ∧ LGraph.CircIffLoop P'.g ∧
    (∀ far k, locCostGeA far k P → P'.LocCostGe far k) ∧
      ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L',
        ∀ far k, R.LocCostGe far k → locCostGeA far k Q

def BAFinalS (R : BAPGraph (Fin 2) → Prop) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (k : ℤ), R P → P.g.LocStd →
    (locCostGeA false k P → k ≤ P.scalingOrder) ∧
      (¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → locCostGeA true k P → k ≤ P.scalingOrder)

def BALocReg6 : Prop :=
  ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
    (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))

/-! ## Target 1: `untag`, normality (no frame-normality hypothesis is needed) -/

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

/-- the premise provers: an `untag` introduction at `BALocStepT`, and `locReg6InvA` at the start terms -/
theorem baUntag_locStepT_intro {P : BAPGraph (Fin 2)} {L : List (BAPGraph (Fin 2))} (hN : P.g.Normal) (h : BALocStep P L) :
    untag BALocStepT P L := (baUntag_locStepT P L).2 ⟨hN, h⟩

theorem baInit_locReg6InvA {p : ℕ} {P0 : BAPGraph (Fin 2)} (h : P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition) : locReg6InvA p P0 :=
  baInit_holds p P0 h

/-! ## Targets 2-3: the bridge, the relabelling and the twist leave the cost invariant -/

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
      show s (g ((promoteC P.g).vmap u)) (g ((promoteC P.g).vmap v)) ↔ s u v
      exact ⟨fun h => s.trans (s.trans hu h) (s.symm hv), fun h => s.trans (s.trans (s.symm hu) h) hv⟩
    refine le_of_le_of_eq (hk (Setoid.comap g s) (fun hf hxy => hfar hf ?_)) ((BAStepS_scost_img P.g (Setoid.comap g s)).trans (by rw [hcomap]))
    rw [← hcomap]
    show (Setoid.comap g s) ((promoteC P.g).vmap (Sum.inl (P.ext 0))) ((promoteC P.g).vmap (Sum.inl (P.ext 1)))
    rw [BAAtomic_vmap_inl, BAAtomic_vmap_inl]
    exact hxy

theorem baEquivCost_holds : BAEquivCost := by
  rintro R S ⟨eE, eI, hext, hsol, ⟨l, hl, hF⟩, -, -⟩ far k
  have hW : (R.g.relabel (Sum.map eE eI)).waved.length = S.g.waved.length := hl.length_eq.symm.trans hF.length_eq
  have hcost : ∀ s : Setoid (S.E' ⊕ S.I'), S.g.scost s = R.g.scost (Setoid.comap (Sum.map eE eI) s) := fun s =>
    (LGraph.scost_perm _ _ hsol hW s).symm.trans
      (LGraph.scost_relabel R.g eE eE.surjective (Sum.map eE eI) (Sum.map_surjective.2 ⟨eE.surjective, eI.surjective⟩) (fun _ => rfl) s)
  have hfar : ∀ s : Setoid (S.E' ⊕ S.I'), Setoid.comap (Sum.map eE eI) s (Sum.inl (R.ext 0)) (Sum.inl (R.ext 1)) ↔
      s (Sum.inl (S.ext 0)) (Sum.inl (S.ext 1)) := fun s => by
    show s (Sum.inl (eE (R.ext 0))) (Sum.inl (eE (R.ext 1))) ↔ _
    rw [hext, hext]
  constructor
  · intro h s hs
    rw [hcost]
    exact h _ (fun hf hxy => hs hf ((hfar s).1 hxy))
  · intro h s hs
    have hrt : ∀ u : R.E' ⊕ R.I', Sum.map eE.symm eI.symm (Sum.map eE eI u) = u := fun u => by cases u <;> simp
    have hcs : Setoid.comap (Sum.map eE eI) (Setoid.comap (Sum.map eE.symm eI.symm) s) = s := by
      ext u v
      show s (Sum.map eE.symm eI.symm (Sum.map eE eI u)) (Sum.map eE.symm eI.symm (Sum.map eE eI v)) ↔ s u v
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

theorem baCostTwist_holds : BACostTwist := by
  intro c t P far k
  have hat : atomSetoid (P.g.twist c t) = atomSetoid P.g := by simp only [atomSetoid, BAGraph.BASymm1_twist_atom]
  exact ⟨fun h s hs hfar => le_of_le_of_eq (h s (hat ▸ hs) hfar) (BAStepS_scostA_twist c t P.g s),
    fun h s hs hfar => le_of_le_of_eq (h s (hat ▸ hs) hfar) (BAStepS_scostA_twist c t P.g s).symm⟩

theorem baShapeLL_twist : ∀ sh : BAShape, BAShapeLL sh BAFrameStepTN → BAShapeLL sh BALocStepT := by
  intro sh h P LT ⟨hN, c, t, LT0, hF, hLT⟩ Q hQ far k hk
  subst hLT
  obtain ⟨⟨sh', Q0⟩, hmem, he⟩ := List.mem_map.1 hQ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact (baCostTwist_holds c t Q0 far k).2 (h (P.twist c t) LT0 ⟨(ba_twist_inv_out c t P.g).2.2.2.2.2 hN, hF⟩ Q0 hmem far k
    ((baCostTwist_holds c t P far k).2 hk))

/-! ## Target 4: `BASimC'` at the tagged step, `P' := (P.twist c t).img` -/

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

/-! ## Target 5: the step from the simulation (T2397 probe 137, per output) -/

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

/-! ## Target 6: `BAFinalS` at `LocStd`, through `P.img` -/

theorem baFinalS_holds (R : BAPGraph (Fin 2) → Prop) : BAFinalS R := by
  intro P k _ hL
  have hstd : P.img.LocStd := (P.g.img_locStd_iff hL.1).1 hL
  have hord : P.img.g.scalingOrder = P.scalingOrder := by
    show ord _ = ord _
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

/-! ## Target 7: the assembly along `BReach`, and the closed form along `BAReach` -/

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

theorem baReach_bReach {K : ℤ} {P0 Q : BAPGraph (Fin 2)} (h0 : P0.g.Normal) (h : BAReach K P0 Q) :
    Q.g.Normal ∧ BReach (untag BALocStepT) P0 Q := by
  induction h with
  | refl => exact ⟨h0, BReach.refl⟩
  | step Q' R L hPQ hlt hstd hls hR ih =>
    have hst : untag BALocStepT Q' L := (baUntag_locStepT Q' L).2 ⟨ih.1, hls⟩
    exact ⟨baNormal_locStepT Q' L hst R hR, BReach.step ih.2 hst hR⟩

/-- the closed form from the proved pieces; the shapes `s1`, `e1` of `BAFrameStepTN` (target 5, stage 1b) stay hypotheses -/
theorem baLocReg6_of_shapes (hs1 : BAShapeLL BAShape.s1 BAFrameStepTN) (he1 : BAShapeLL BAShape.e1 BAFrameStepTN) : BALocReg6 := by
  intro p P0 hP0 hX K Q hQ
  have hX' : ∀ sh, sh ≠ BAShape.band → BAShapeLL sh BALocStepT := by
    intro sh hsh
    refine baShapeLL_twist sh ?_
    cases sh with
    | band => exact absurd rfl hsh
    | s1 => exact hs1
    | e1 => exact he1
    | e2 => exact hX _ (Or.inl rfl)
    | macroA => exact hX _ (Or.inr (Or.inl rfl))
    | macroB => exact hX _ (Or.inr (Or.inr rfl))
  exact ba_ord_ge_of_simC' 0 p BALocStepT P0 (baInit_locReg6InvA hP0) baNormal_locStepT (baSimC'_holds 0) hX' (baFinalS_holds _) Q
    (baReach_bReach (BAGraph.partition_normal _ P0 hP0) hQ).2

/-! ## Nonempty instances (target 8): the twists `(true, true)` of `P_B` (`within`) and `P_C` (`ggSplit`, `j = 0`), and a `LocStd` graph -/

section Inst
open BASimInst BALvl1AInst

def LTB : List (BAShape × BAPGraph (Fin 2)) := ((baPG baPB).withinOutsT pB).map fun x => (x.1, BAPGraph.twist true true x.2)
def LTC : List (BAShape × BAPGraph (Fin 2)) := ((baPG baPC).splitOutsT pC qC 0).map fun x => (x.1, BAPGraph.twist true true x.2)

theorem stepB : BALocStepT ((baPG baPB).twist true true) LTB := ⟨normalB, true, true, _, by rw [BALvl1A_twist_invol]; exact hTB, rfl⟩
theorem stepC : BALocStepT ((baPG baPC).twist true true) LTC := ⟨normalC, true, true, _, by rw [BALvl1A_twist_invol]; exact hTC, rfl⟩

/-- the outputs carry the tags the pins read: `band` (target 4), `e1`, `e2`, `macroA`, `macroB` (target 5, closed form) -/
example : (BAShape.band ∈ LTB.map Prod.fst ∧ BAShape.e2 ∈ LTB.map Prod.fst ∧ BAShape.macroA ∈ LTB.map Prod.fst) ∧
    (BAShape.band ∈ LTC.map Prod.fst ∧ BAShape.e1 ∈ LTC.map Prod.fst ∧ BAShape.e2 ∈ LTC.map Prod.fst ∧ BAShape.macroB ∈ LTC.map Prod.fst) := by
  decide +kernel

/-- target 1: `untag` of `BALocStepT` at the step is R1's `BALocStep` (`locStepB`, `locStepC`), and the `untag` prover gives the step -/
example : untag BALocStepT ((baPG baPB).twist true true) (((baPG baPB).withinOuts pB).map (BAPGraph.twist true true)) ∧
    untag BALocStepT ((baPG baPC).twist true true) (((baPG baPC).splitOuts pC qC 0).map (BAPGraph.twist true true)) :=
  ⟨(baUntag_locStepT _ _).2 ⟨normalB, locStepB⟩, (baUntag_locStepT _ _).2 ⟨normalC, locStepC⟩⟩

/-- target 4 at the two steps: a band graph `P'`, normal, and for a `band` output `Q` a `LocStep` output `R` whose costs give those of `Q` -/
example (m : ℂ) : (∃ P' : PGraph (Fin 2), P'.g.Normal ∧ ∃ Q, (BAShape.band, Q) ∈ LTB ∧ ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L',
      ∀ far k, R.LocCostGe far k → locCostGeA far k Q) ∧
    (∃ P' : PGraph (Fin 2), P'.g.Normal ∧ ∃ Q, (BAShape.band, Q) ∈ LTC ∧ ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L',
      ∀ far k, R.LocCostGe far k → locCostGeA far k Q) := by
  obtain ⟨P', hN, -, -, hR⟩ := baSimC'_holds m _ _ stepB
  obtain ⟨P'', hN', -, -, hR'⟩ := baSimC'_holds m _ _ stepC
  obtain ⟨Q, hQ⟩ := tag_exists LTB .band (by decide +kernel)
  obtain ⟨Q', hQ'⟩ := tag_exists LTC .band (by decide +kernel)
  exact ⟨⟨P', hN, Q, hQ, hR Q hQ⟩, ⟨P'', hN', Q', hQ', hR' Q' hQ'⟩⟩

/-- target 2 at `P_B`; target 3 at its twist -/
example (far : Bool) (k : ℤ) : (locCostGeA far k (baPG baPB) ↔ PGraph.LocCostGe far k (baPG baPB).img) ∧
    (locCostGeA far k ((baPG baPB).twist true true) ↔ locCostGeA far k (baPG baPB)) := ⟨baBridge_holds _ far k, baCostTwist_holds true true _ far k⟩

/-- target 5 at the step at the twist of `P_B`: the cost bound passes to every output (`hX`: the shape inputs, 1b and T2426 O2) -/
example (hX : ∀ sh, sh ≠ BAShape.band → BAShapeLL sh BALocStepT) (far : Bool) (k : ℤ) (hk : locCostGeA far k ((baPG baPB).twist true true)) :
    ∀ Q ∈ ((baPG baPB).withinOuts pB).map (BAPGraph.twist true true), locCostGeA far k Q :=
  baStep_of_simC' 0 BALocStepT (baSimC'_holds 0) hX _ _ ((baUntag_locStepT _ _).2 ⟨normalB, locStepB⟩) far k hk

/-- a locally standard graph with distinct external atoms (`E = Fin 2`, `I = Fin 3`: blue `x → a`, red `y → a`, the atom `{b, c}` by an `M`-dot, five waved edges) -/
def pL : BAPGraph (Fin 2) := baPG (⟨⟨[⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inl 1, .inr 0⟩],
  [⟨false, true, .inl 0, .inr 1⟩, ⟨false, true, .inl 1, .inr 2⟩, ⟨false, true, .inr 0, .inr 1⟩, ⟨false, true, .inr 0, .inr 2⟩, ⟨false, true, .inl 0, .inl 1⟩], [], 1⟩,
  [], [⟨true, .inr 1, .inr 2⟩]⟩ : BAGraph (Fin 2) (Fin 3))

/-- target 6 at `pL` (`ord = 8`, `2p = 4`, `3p = 6` at `p = 2`): the hypotheses `LocStd`, distinct external atoms by `decide`; the cost bound gives `k ≤ ord` -/
example (far : Bool) (k : ℤ) (hk : locCostGeA far k pL) : pL.g.LocStd ∧ pL.scalingOrder = 8 ∧
    ¬ atomSetoid pL.g (Sum.inl (pL.ext 0)) (Sum.inl (pL.ext 1)) ∧ k ≤ pL.scalingOrder := by
  refine ⟨by decide, by decide +kernel, by rw [BAAtomic_atomSetoid_iff, ← BAGraph.BAAtomic_sameAtom_iff]; decide, ?_⟩
  cases far
  · exact (baFinalS_holds (· = pL) pL k rfl (by decide)).1 hk
  · exact (baFinalS_holds (· = pL) pL k rfl (by decide)).2 (by rw [BAAtomic_atomSetoid_iff, ← BAGraph.BAAtomic_sameAtom_iff]; decide) hk

/-- target 7 at `p = 2`: a start term `P0` exists, and the closed form gives (6) at it (`BAReach.refl`); the shapes `s1`, `e1` and the T2426 O2 inputs stay hypotheses -/
example (hs1 : BAShapeLL BAShape.s1 BAFrameStepTN) (he1 : BAShapeLL BAShape.e1 BAFrameStepTN)
    (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) :
    ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → locReg6InvA 2 Q := by
  have hne : (BAGraph.ofLGraph (fxyPowGraph 2)).partition ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [BAGraph.partition, List.length_map] at this
    revert this
    decide
  obtain ⟨P0, hP0⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨P0, hP0, fun K Q hQ => (baLocReg6_of_shapes hs1 he1 2 P0 hP0 hX K Q hQ).1⟩

end Inst

end RBM.Graph

end

open RBM.Graph

#check @BAFrameStepTN
#check @BALocStepT
#check @BASimC'
#check @BAFinalS
#check @BALocReg6
#check @baUntag_locStepT
#check @baNormal_locStepT
#check @baBridge_holds
#check @baEquivCost_holds
#check @baCostTwist_holds
#check @baShapeLL_twist
#check @baSimC'_holds
#check @baStep_of_simC'
#check @baFinalS_holds
#check @ba_ord_ge_of_simC'
#check @baReach_bReach
#check @baLocReg6_of_shapes
#check @baUntag_locStepT_intro
#check @baInit_locReg6InvA

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ours := env.constants.map₂.toList.filter fun (n, ci) =>
    (`RBM.Graph).isPrefixOf n && !n.isInternalDetail && (match ci with | .thmInfo _ => true | _ => false)
  let mut bad : Array Name := #[]
  for (n, _) in ours do
    let axs ← collectAxioms n
    if axs.any fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a) then bad := bad.push n
  -- the premise scan of `#assert_rbm_axioms` (`Test/Axioms.lean`), restricted to `RBM.Graph` (the other modules are not imported here)
  let found := RBM.Audit.scanPremises env (fun n => (`RBM.Audit).isPrefixOf n) (fun n => RBM.Audit.certificates.any fun (_, c) => c == n)
  let classified := RBM.Audit.borrowedProps ++ RBM.Audit.owedProps ++ RBM.Audit.structuralProps ++ RBM.Audit.refutedProps ++ RBM.Audit.supersededProps
  logInfo m!"theorems of this file: {ours.length}; outside the standard axioms: {bad}; unregistered unproved premises in RBM.Graph: {found.filter fun n => (`RBM.Graph).isPrefixOf n && !classified.contains n}"
