/-
Release check for T2443 (dispatcher V3, Mon Oct 12 06:18 UTC 2026; DECISIONS §252).  BA-L L3b4′ `BAStepS′`: property (6) at BA under S′: the tagged step
`BALocStepT`, `BASimC'` from R1 (supervisor 0951 L4-C1), `BABridge` (m3), `BAFinal` at `BAGraph.LocStd` (L4-C3), the assembly along `BAReach`.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2443_`; the 1b names them `BAFrameStepTN`, `BALocStepT`, `BABridge`,
`BASimC'`, `BAFinalS` or as the probe fixes; content binding unless the probe changes it).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2443-check.lean
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

set_option linter.style.longLine false
noncomputable section
open RBM RBM.Graph

/-! ## Part 1: merged names -/
-- R1 (T2423, `Graph/BASim*`): the frame steps, tagged and untagged, R1's relation, the matching, the twist of a packed graph, the instance data
#check @RBM.Graph.BAFrameStep
#check @RBM.Graph.BAFrameStepT
#check @RBM.Graph.BAFrameStepT.within
#check @RBM.Graph.BAFrameStepT.ggSplit
#check @RBM.Graph.BAPGraph.outsT
#check @RBM.Graph.BAPGraph.withinOutsT
#check @RBM.Graph.BAPGraph.splitOutsT
#check @RBM.Graph.BAGraph.tagStd
#check @RBM.Graph.BAGraph.tagT1
#check @RBM.Graph.BAFrameStepT_untag
#check @RBM.Graph.baFrameStepT_untag_holds
#check @RBM.Graph.PGraph.BAEquiv
#check @RBM.Graph.PGraph.BAEquivC
#check @RBM.Graph.PGraph.BASim_BAEquiv_toC
#check @RBM.Graph.BAMatch
#check @RBM.Graph.baMatch_holds
#check @RBM.Graph.BAExtraGood
#check @RBM.Graph.baExtraGood_holds
#check @RBM.Graph.BAsim'
#check @RBM.Graph.baSim'_holds
#check @RBM.Graph.BAPGraph.twist
#check @RBM.Graph.BASimInst.baPB
#check @RBM.Graph.BASimInst.pB
#check @RBM.Graph.BASimInst.baPC
#check @RBM.Graph.BASimInst.pC
#check @RBM.Graph.BASimInst.qC
#check @RBM.Graph.BASimInst.hTB
#check @RBM.Graph.BASimInst.hTC
-- L3a3 (T2440, `Graph/BALvl1A`): the BA step and reachability, the instances at the twists of `P_B`, `P_C`
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BALvl1A_reach_refl
#check @RBM.Graph.BALvl1AInst.locStepB
#check @RBM.Graph.BALvl1AInst.locStepC
#check @RBM.Graph.BALvl1AInst.normalB
#check @RBM.Graph.BALvl1AInst.normalC
-- L3b3′ (T2426, `Graph/BAScost`, `BAScost2`): the cost vocabulary at atoms, `BReach` (a `ReflTransGen` definition), the pins, the shapes
#check @RBM.Graph.scostA
#check @RBM.Graph.locStdA
#check @RBM.Graph.locCostGeA
#check @RBM.Graph.locReg6InvA
#check @RBM.Graph.BReach
#check @RBM.Graph.BReach.refl
#check @RBM.Graph.BReach.step
#check @RBM.Graph.BReach.ind
#check @RBM.Graph.BAInit
#check @RBM.Graph.baInit_holds
#check @RBM.Graph.BAFinal
#check @RBM.Graph.BAStep
#check @RBM.Graph.BANormal
#check @RBM.Graph.BAScostLL
#check @RBM.Graph.BAScostLL_splitG
#check @RBM.Graph.BAScostLL_of_band
#check @RBM.Graph.BAShape
#check @RBM.Graph.BTStep
#check @RBM.Graph.untag
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BAScost_pack
#check @RBM.Graph.BAScost_locCostGeA_term
#check @RBM.Graph.BAScost_Term
#check @RBM.Graph.baShapeLL_of_terms
#check @RBM.Graph.baShapeLL_s1
#check @RBM.Graph.baShapeLL_e1
#check @RBM.Graph.baShapeLL_e2
#check @RBM.Graph.baShapeLL_macroA
#check @RBM.Graph.baShapeLL_macroB
#check @RBM.Graph.BAGraph.BAScost_trA
#check @RBM.Graph.BAGraph.BAScost_trB
-- R0 (T2417, `Graph/BAAtomic`): atoms, the one image map, its normality, counters and `LocStd` transfer
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.promoteC
#check @RBM.Graph.BAGraph.img
#check @RBM.Graph.BAPGraph.img
#check @RBM.Graph.BAGraph.img_normal
#check @RBM.Graph.BAGraph.img_counters
#check @RBM.Graph.BAGraph.img_locStd_iff
#check @RBM.Graph.BAimg
#check @RBM.Graph.BAimg_holds
#check @RBM.Graph.BAImgCounters
#check @RBM.Graph.BAImgCounters_holds
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.BAGraph.sameAtom
#check @RBM.Graph.BAGraph.intAtom
#check @RBM.Graph.BAGraph.atEdges
#check @RBM.Graph.BAGraph.atCharge
#check @RBM.Graph.BAGraph.nExt
#check @RBM.Graph.baPG
-- packed graphs, order, partition, start graph (`BAVocab`, `LocalRegular`)
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAPGraph.counters
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.ofLGraph
#check @RBM.Graph.fxyPowGraph
-- L3a1, L3a2 (T2425, T2432): the twist keeps atoms, normality, counters
#check @RBM.Graph.BAGraph.twist
#check @RBM.Graph.BAGraph.BASymm1_twist_atom
#check @RBM.Graph.BAGraph.BASymm1_twist_sameAtom
#check @RBM.Graph.baTwistInv_holds
#check @RBM.Graph.ba_twist_inv_out
#check @RBM.Graph.BAGraph.twist_invol
-- the band: cost, its relabelling, permutation and twist; the invariant, the step lemma, the final step
#check @RBM.Graph.LGraph.scost
#check @RBM.Graph.LGraph.scost_perm
#check @RBM.Graph.LGraph.scost_relabel
#check @RBM.Graph.LGraph.scost_twist
#check @RBM.Graph.lwSymmTwistG
#check @RBM.Graph.LGraph.CircIffLoop
#check @RBM.Graph.LGraph.ScostLL
#check @RBM.Graph.PGraph.LocCostGe
#check @RBM.Graph.LocStep
#check @RBM.Graph.locCostGe_locStep
#check @RBM.Graph.localReg6d_locCostGe_term
#check @RBM.Graph.locReg6_of_locCostGe
#check @RBM.Graph.locReg6far_of_locCostGe
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.PGraph.LocStd
#check @RBM.Graph.PGraph.lvl1Comp

/-! ## Part 2: the target statements (Prop values; no proof; the probe fixes the text) -/

/-- Target 1 (`BAFrameStepTN`): the tagged frame step at a normal packed graph over `Fin 2`. -/
def T2443_FrameT : BTStep := fun P LT => P.g.Normal ∧ BAFrameStepT P LT

/-- Target 1 (`BALocStepT`): at a normal graph, a tagged frame step at the twist, every output twisted back, the tags kept. -/
def T2443_LocStepT : BTStep := fun P LT =>
  P.g.Normal ∧ ∃ (c t : Bool) (LT0 : List (BAShape × BAPGraph (Fin 2))),
    BAFrameStepT (P.twist c t) LT0 ∧ LT = LT0.map (fun x => (x.1, BAPGraph.twist c t x.2))

/-- Target 1: forgetting the tags gives `BALocStep` at a normal graph. -/
def T2443_Untag : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), untag T2443_LocStepT P L ↔ P.g.Normal ∧ BALocStep P L

/-- Target 2 (`BABridge`, T2397 probe 111 with the merged `BAPGraph.img`): the cost at atoms is the band cost on the image. -/
def T2443_Bridge : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k P ↔ PGraph.LocCostGe far k P.img

/-- Target 2: the band invariant is invariant under R1's relation (waved colours not read; `BAEquiv` by `PGraph.BASim_BAEquiv_toC`). -/
def T2443_EquivCost : Prop :=
  ∀ (R S : PGraph (Fin 2)), R.BAEquivC S → ∀ (far : Bool) (k : ℤ), (R.LocCostGe far k ↔ S.LocCostGe far k)

/-- Target 3: the cost at atoms is invariant under the twist (`LGraph.scost_twist`, `BAGraph.BASymm1_twist_atom`). -/
def T2443_CostTwist : Prop :=
  ∀ (c t : Bool) (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k (P.twist c t) ↔ locCostGeA far k P

/-- Target 3: a shape lemma at the frame level passes to the twisted step. -/
def T2443_ShapeTwist : Prop :=
  ∀ sh : BAShape, BAShapeLL sh T2443_FrameT → BAShapeLL sh T2443_LocStepT

/-- Target 4 (`BASimC'`, `T2423-prove.md:240-242`): the simulation up to relabelling, cost half, the band step chosen per output. -/
def T2443_SimC (m : ℂ) (T : BTStep) : Prop :=
  ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), P'.g.Normal ∧ LGraph.CircIffLoop P'.g ∧
    (∀ far k, locCostGeA far k P → P'.LocCostGe far k) ∧
      ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L',
        ∀ far k, R.LocCostGe far k → locCostGeA far k Q

/-- Target 5 (`baStep_of_simC'`, T2397 probe 137 per output): the step pin from the simulation and the shape lemmas. -/
def T2443_StepOfSimC : Prop :=
  ∀ (m : ℂ) (T : BTStep), T2443_SimC m T → (∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) → BAStep (untag T)

/-- Target 6 (`BAFinalS`, L4-C3): the merged `BAFinal` with atom-level `BAGraph.LocStd` in place of vertex-level `locStdA`. -/
def T2443_Final (R : BAPGraph (Fin 2) → Prop) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (k : ℤ), R P → P.g.LocStd →
    (locCostGeA false k P → k ≤ P.scalingOrder) ∧
      (¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → locCostGeA true k P → k ≤ P.scalingOrder)

/-- Target 7 (`ba_ord_ge_of_simC'`, T2397 probe 95 + 148 per output, at `LocStd`). -/
def T2443_OrdGe : Prop :=
  ∀ (m : ℂ) (p : ℕ) (T : BTStep) (P0 : BAPGraph (Fin 2)), locReg6InvA p P0 → BANormal (untag T) → T2443_SimC m T →
    (∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) → T2443_Final (BReach (untag T) P0) → ∀ Q, BReach (untag T) P0 Q →
      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))

/-- Target 7, closed form (`baLocReg6_reach`): (6) at every graph reached by `BAReach` from a start term; hypotheses: frame normality
(the first conjunct of L3a4's `BAstepMono`) and the three shapes whose inputs are open (T2426 audit O2). -/
def T2443_LocReg6 : Prop :=
  ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
    (∀ (P : BAPGraph (Fin 2)) (outs : List (BAPGraph (Fin 2))), BAFrameStep P outs → P.g.Normal → ∀ Q ∈ outs, Q.g.Normal) →
    (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh T2443_FrameT) →
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
      locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧
        (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))

/-- Statement level: target 4 at the tagged BA step, target 5's two closed shapes, target 6 at every `R`. -/
example : Prop := ∀ m : ℂ, T2443_SimC m T2443_LocStepT
example : Prop := BAShapeLL BAShape.s1 T2443_FrameT ∧ BAShapeLL BAShape.e1 T2443_FrameT
example : Prop := ∀ R : BAPGraph (Fin 2) → Prop, T2443_Final R
/-- Target 8 at the twist of R1's macro datum `P_B` (`within`; `BALvl1AInst.locStepB` untagged). -/
example : Prop :=
  T2443_LocStepT ((baPG BASimInst.baPB).twist true true)
    (((baPG BASimInst.baPB).withinOutsT BASimInst.pB).map (fun x => (x.1, BAPGraph.twist true true x.2)))
