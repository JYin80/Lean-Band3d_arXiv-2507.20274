/-
Release check for T2469 (dispatcher V3, Mon Oct 12 18:07 UTC 2026; DECISIONS §274).  BA-L L3b2 `BALocReg2`: the moved targets 3 (c)-(e) of L3b1 (T2456 split Σ,
DECISIONS §269 (7); supervisor 0948 O2R-C4): `BAShapePath` for `e2`, `macroA`, `macroB`; the binder-free path step and (1)-(5) contract (the BA twin of
`LocalRegular2` under S′); the composed statement `BALocRegConcl` plus (1)-(5) for the outputs (DECISIONS §265 (4)), with the shape binder of T2448
discharged (0948 O2R-C3, 1152 :188).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2469_`; content binding; the 1b names them as the ticket proposes or as
the 1a fixes) and shapes (not binding) of the term input, the stage-2 intermediates, the consumer reading and the instance data.
Merged names only.  No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2469-check.lean
-/
import RBM3D.Graph.BALocReg1B
import RBM3D.Graph.BALocReg1
import RBM3D.Graph.BAShapeO2B
import RBM3D.Graph.BAShapeO2
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BAScost
import RBM3D.Graph.BAScost2
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAAtomic2
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BALvl1C
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BASymm1
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LocalRegular
import RBM3D.Graph.LocalRegular2
import RBM3D.Gauss.FineModel
import RBM3D.BA.CouplingWindow

set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open RBM RBM.Gauss RBM.Graph

/-! ## Part 1: merged names -/
-- the band (`LocalRegular`, `LocalRegular2`): predicates (1)-(5), the coloured path invariant, its stage tools, the 17 term results of §3, the step,
-- the start, (3)-(5) at `LocStd`, the expansion statement and its instance
#check @RBM.Graph.PGraph.LocReg1
#check @RBM.Graph.PGraph.LocReg2
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.PGraph.PathInv2
#check @RBM.Graph.LGraph.localReg2_PathFam
#check @RBM.Graph.localReg2_Fam
#check @RBM.Graph.localReg2_Fam.map
#check @RBM.Graph.localReg2_Fam.of_add_diag
#check @RBM.Graph.localReg2_Fam.add_diag
#check @RBM.Graph.localReg2_Fam.flip
#check @RBM.Graph.localReg2_Fam.thr
#check @RBM.Graph.LGraph.localReg2_pathFam_map
#check @RBM.Graph.LGraph.localReg2_pathFam_partition
#check @RBM.Graph.localReg2_pathFam_owxT1
#check @RBM.Graph.localReg2_pathFam_owxT2
#check @RBM.Graph.localReg2_pathFam_owxT3
#check @RBM.Graph.localReg2_pathFam_owxT4
#check @RBM.Graph.localReg2_pathFam_oe1xOwx
#check @RBM.Graph.localReg2_pathFam_oe1xD
#check @RBM.Graph.localReg2_pathFam_oe2xR2
#check @RBM.Graph.localReg2_pathFam_oe2xR3
#check @RBM.Graph.localReg2_pathFam_oe2xR4
#check @RBM.Graph.localReg2_pathFam_oe2xR5
#check @RBM.Graph.localReg2_pathFam_oe2xR6
#check @RBM.Graph.localReg2_pathFam_oe2xR7
#check @RBM.Graph.localReg2_pathFam_oe2xR8
#check @RBM.Graph.pathInv2_locStep
#check @RBM.Graph.fxyPowGraph_pathInv2
#check @RBM.Graph.PGraph.PathInv2.locReg345
#check @RBM.Graph.LGraph.molNV_le_molNW_add_one
#check @RBM.Graph.lw_localregular_upto5
#check @RBM.Graph.localReg2_inst_expansion
#check @RBM.Graph.localReg2_inst_Q_locReg345
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.lvl1Cutoff
-- L3b1 (T2456, `BALocReg1`, `BALocReg1B`, merged 3bb131d): the path tools at the atomic image, the shapes `s1`, `e1`, the step and the contract with the
-- binder `hX`, the start, the start bound, the shadow bridge, the reached locally standard graph, the instance data
#check @RBM.Graph.BALocReg1_mu
#check @RBM.Graph.BALocReg1_PathAt
#check @RBM.Graph.BALocReg1_img_pathInv2_iff
#check @RBM.Graph.BALocReg1_pathAt_map
#check @RBM.Graph.BALocReg1_pathAt_partition
#check @RBM.Graph.BALocReg1_pathInv2_pack
#check @RBM.Graph.BALocReg1_pathAt_ext
#check @RBM.Graph.BALocReg1_pathAt_lanlwT1
#check @RBM.Graph.BALocReg1_pathAt_twist
#check @RBM.Graph.baEquivPath_holds
#check @RBM.Graph.baPathTwist_holds
#check @RBM.Graph.BAShapePath
#check @RBM.Graph.baShapePath_s1_tn
#check @RBM.Graph.baShapePath_e1_tn
#check @RBM.Graph.baShapePath_twist
#check @RBM.Graph.BASimP'
#check @RBM.Graph.baSimP'_holds
#check @RBM.Graph.BAPathStep
#check @RBM.Graph.baPathStep_of_simP'
#check @RBM.Graph.baPathStep_holds
#check @RBM.Graph.BAPathInit
#check @RBM.Graph.baPathInit_holds
#check @RBM.Graph.baStart_nM_le
#check @RBM.Graph.baShadow_locReg345
#check @RBM.Graph.BALocReg15
#check @RBM.Graph.baLocReg15_holds
#check @RBM.Graph.ba_fxyPow_integral_eq
#check @RBM.Graph.BALocReg1B_start_step
#check @RBM.Graph.BALocReg1B_reach_locStd
#check @RBM.Graph.BALocReg1Inst.baPEr
#check @RBM.Graph.BALocReg1Inst.pEr
#check @RBM.Graph.BALocReg1Inst.outsEr
#check @RBM.Graph.BALocReg1Inst.hStepEr
#check @RBM.Graph.BALocReg1Inst.normalEr
#check @RBM.Graph.BALocReg1Inst.pathInv2_Er
#check @RBM.Graph.BALocReg1Inst.tags_Er
#check @RBM.Graph.BALocReg1Inst.LCr
#check @RBM.Graph.BALocReg1Inst.LCr_pathFam
#check @RBM.Graph.BALocReg1Inst.pathInv2_C
-- L3b4″ (T2447, `BAShapeO2`, `BAShapeO2B`, merged 00f4a10): the cost side of the same shapes, per term; stage 2; the three `_tn`; (6) closed
#check @RBM.Graph.BAShapeO2_psi2
#check @RBM.Graph.BAShapeO2_lanlwD
#check @RBM.Graph.BAShapeO2_withinHead
#check @RBM.Graph.BAShapeO2_lw2Head
#check @RBM.Graph.BAShapeO2_lw4Head
#check @RBM.Graph.BAShapeO2_lw4Tail
#check @RBM.Graph.BAShapeO2_ggA2
#check @RBM.Graph.BAShapeO2_ggA3
#check @RBM.Graph.BAShapeO2_ggA4
#check @RBM.Graph.BAShapeO2_ggA5
#check @RBM.Graph.BAShapeO2_ggAD
#check @RBM.Graph.BAShapeO2_ggB1
#check @RBM.Graph.BAShapeO2_ggB2
#check @RBM.Graph.BAShapeO2_ggBD
#check @RBM.Graph.BAShapeO2_ggSplitD1
#check @RBM.Graph.BAShapeO2_ggSplitD2
#check @RBM.Graph.BAShapeO2_ggSplitD3
#check @RBM.Graph.BAShapeO2_ggSplitD4
#check @RBM.Graph.BAShapeO2_lw2
#check @RBM.Graph.BAShapeO2_lw4
#check @RBM.Graph.BAShapeO2_within
#check @RBM.Graph.BAShapeO2_gg2
#check @RBM.Graph.BAShapeO2_gg4
#check @RBM.Graph.BAShapeO2B_ext_normal
#check @RBM.Graph.BAShapeO2B_lwSplit_last
#check @RBM.Graph.BAShapeO2B_macroA
#check @RBM.Graph.BAShapeO2B_macroB
#check @RBM.Graph.baShapeLL_e2_tn
#check @RBM.Graph.baShapeLL_macroA_tn
#check @RBM.Graph.baShapeLL_macroB_tn
#check @RBM.Graph.baLocReg6_holds
-- L3b3′, L3b4′ (T2426, T2443: `BAScost`, `BAScost2`, `BAStepS`): shapes, tagged steps, terms, packing, the transfer graphs, reachability
#check @RBM.Graph.BAShape
#check @RBM.Graph.BTStep
#check @RBM.Graph.untag
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BAScostLL
#check @RBM.Graph.BAScostLL_S1
#check @RBM.Graph.BAScostLL_macroA
#check @RBM.Graph.BAScostLL_macroB
#check @RBM.Graph.BAScost_psi1
#check @RBM.Graph.BAScost_rho2
#check @RBM.Graph.BAScost_lanlwT1_eq
#check @RBM.Graph.BAScost_atomSetoid_ext
#check @RBM.Graph.BAScost_pack
#check @RBM.Graph.BAScost_locCostGeA_term
#check @RBM.Graph.BAGraph.BAScost_trA
#check @RBM.Graph.BAGraph.BAScost_trB
#check @RBM.Graph.BAScost_Term
#check @RBM.Graph.baShapeLL_of_terms
#check @RBM.Graph.baShapeLL_e2
#check @RBM.Graph.baShapeLL_macroA
#check @RBM.Graph.baShapeLL_macroB
#check @RBM.Graph.BAFrameStepTN
#check @RBM.Graph.BALocStepT
#check @RBM.Graph.baUntag_locStepT
#check @RBM.Graph.baNormal_locStepT
#check @RBM.Graph.baShapeLL_twist
#check @RBM.Graph.BALocReg6
#check @RBM.Graph.baLocReg6_reach
#check @RBM.Graph.BReach
#check @RBM.Graph.BReach.ind
#check @RBM.Graph.baReach_bReach
-- R1 (`BASim`, `BASim3`): the tagged frame step, its outputs, tags, the builders, the witnesses
#check @RBM.Graph.BAFrameStepT
#check @RBM.Graph.BAPGraph.outsT
#check @RBM.Graph.BAPGraph.withinOutsT
#check @RBM.Graph.BAPGraph.splitOutsT
#check @RBM.Graph.BAGraph.tagStd
#check @RBM.Graph.BAGraph.tagT1
#check @RBM.Graph.BAGraph.extraB
#check @RBM.Graph.BAGraph.ext
#check @RBM.Graph.BAGraph.lanlwD
#check @RBM.Graph.BAGraph.lanlwT1
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.baMatch_holds
#check @RBM.Graph.BASimInst.baPA
#check @RBM.Graph.BASimInst.pA
#check @RBM.Graph.BASimInst.ggFT
#check @RBM.Graph.BASimInst.hTA
#check @RBM.Graph.BASimInst.baPB
#check @RBM.Graph.BASimInst.pB
#check @RBM.Graph.BASimInst.hTB
#check @RBM.Graph.BASimInst.baPC
#check @RBM.Graph.BASimInst.pC
#check @RBM.Graph.BASimInst.qC
#check @RBM.Graph.BASimInst.hTC
#check @RBM.Graph.BASimInst.tag_exists
-- L3d3 (T2448, `BAEngine`, merged 79f3c1c): the conclusion, the assembly and the engine with the binder `T2448_Binder`, black waved edges, `LocStd` producer
#check @RBM.Graph.BALocRegConcl
#check @RBM.Graph.baEngine_assemble
#check @RBM.Graph.ba_localregularX
#check @RBM.Graph.baStart_nWS
#check @RBM.Graph.ba_nWS_ge
#check @RBM.Graph.BAEngine_pL
#check @RBM.Graph.BAEngine_pL_locStd
-- vocabulary, reachability, atoms, shadow, data
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.img
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.BAGraph.img_locStd_iff
#check @RBM.Graph.BAGraph.img_molOf_eq_iff
#check @RBM.Graph.BAAtomic_pathFam_iff
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.baPG
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.ofLGraph
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BAComb.val
#check @RBM.Graph.BAlwData
#check @RBM.Graph.BASymm1Inst.ℓ0
#check @RBM.BA.CouplingWindowInst.flowP_data
#check @RBM.Gauss.PF

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- Target 1 (c) (`baShapePath_e2_tn`; = `T2456_E2Path` up to unfolding `BAShapePath`, moved here under split Σ, DECISIONS §269 (7); 0948 O2R-C4). -/
def T2469_E2Path : Prop := BAShapePath BAShape.e2 BAFrameStepTN

/-- Target 1 (c) (`baShapePath_macroA_tn`; = `T2456_MacroAPath`): stage 2 of `within`. -/
def T2469_MacroAPath : Prop := BAShapePath BAShape.macroA BAFrameStepTN

/-- Target 1 (c) (`baShapePath_macroB_tn`; = `T2456_MacroBPath`): stage 1 `d2`-`d4` and stage 2 of `ggSplit`. -/
def T2469_MacroBPath : Prop := BAShapePath BAShape.macroB BAFrameStepTN

/-- Target 1 (d) (`baPathBinder_holds`): the hypothesis `hX` of `baPathStep_holds` (`BALocReg1:631`) and of `baLocReg15_holds` (`BALocReg1B:264`),
verbatim (= `T2456_PathBinder`). -/
def T2469_PathBinder : Prop :=
  ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN

/-- Target 2 (`baPathStep_closed`): the path step of the tagged BA step, no hypothesis (band `pathInv2_locStep`, `LocalRegular2:1582`). -/
def T2469_PathStep : Prop := BAPathStep (untag BALocStepT)

/-- Target 2 (`baLocReg15_closed`): the contract (1)-(5) of L3b1 (`BALocReg1B:254`), no hypothesis. -/
def T2469_LocReg15 : Prop := BALocReg15

/-- Target 3 (a) (`baShapeLLBinder_holds`): the shape binder of `baEngine_assemble` and `ba_localregularX` (`BAEngine:268, 335`), verbatim
(= `T2448_Binder`; 0948 O2R-C3); its content is the closing step inside `baLocReg6_holds` (`BAShapeO2B:356-359`). -/
def T2469_Binder6 : Prop :=
  ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN

/-- Target 3 (b) (`baLocRegConcl_upto5`; DECISIONS §265 (4), 1152 :189-191): any lists with `BALocRegConcl` carry (1)-(5): the path invariant, `n_M ≤ p`
and `LocReg2` on the image at every graph (conjunct (c) gives the start term and `BAReach`), and at the outputs (locally standard from conjunct (a)) (1) on
the image and (3)-(5) on the image and on the shadow. -/
def T2469_ConclUpto5 : Prop :=
  ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))), BALocRegConcl p c K0 d D outs errs →
    (∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p) ∧
      ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p

/-- Target 3 (c) (`ba_localregular_upto5`; twin of `lw_localregular_upto5`, `LocalRegular2:1857`): one pair of lists with `BALocRegConcl`, at least `p`
black waved edges in every graph (as `ba_localregularX`), and the conclusions of target 3 (b); no binder. -/
def T2469_Upto5 : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ (∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)) ∧
      (∀ Q ∈ outs ++ errs, Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p) ∧
        ∀ Q ∈ outs, PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p

/-- Statement level (not binding): the three shapes give the binder; the binder closes L3b1's step and contract; the contract gives target 3 (b);
with the T2448 binder (target 3 (a)) the engine gives target 3 (c). -/
example : Prop := T2469_E2Path → T2469_MacroAPath → T2469_MacroBPath → T2469_PathBinder
example : Prop := T2469_PathBinder → T2469_PathStep
example : Prop := T2469_PathBinder → T2469_LocReg15
example : Prop := T2469_LocReg15 → T2469_ConclUpto5
example : Prop := T2469_Binder6 → T2469_ConclUpto5 → T2469_Upto5

/-- Shape (not binding) of the term input of target 1 (c) (the path twin of `baShapeLL_e2`, `BAScost2:93`, with `BALocReg1_PathAt` in place of
`BAScostLL`): an `e2` output is a packed partition term of a builder term `X` whose image carries the invariant of the image of `P`. -/
example : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (BAShape.e2, Q) ∈ LT →
    ∃ X : BAScost_Term P, (∀ k : ℕ, BALocReg1_PathAt P.g k (P.ext 0) (P.ext 1) → BALocReg1_PathAt X.X k (P.ext 0) (P.ext 1)) ∧
      ∃ Q0 ∈ X.X.partition, Q = BAScost_pack P Q0

/-- Target 1 (b) shapes (not binding): the macro (a) intermediate (the path twin of `BAScostLL_macroA`, `BAScost:1057`) and the macro (b)
intermediate (of `BAScostLL_macroB`, `BAScost:1237`): the invariant passes from `Γ` to the transfer graph. -/
example : Prop :=
  ∀ (E I : Type) [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))),
    p ∈ lwSplit Γ.solid → (p.1.σ = true ∧ p.1.circ = true) →
      ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (Γ.BAScost_trA p) k a b
example : Prop :=
  ∀ (E I : Type) [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))),
    p ∈ lwSplit Γ.solid → q ∈ lwSplit p.2 → (p.1.σ = true ∧ p.1.circ = true) → (q.1.σ = true ∧ q.1.circ = true) →
      Γ.sameAtom p.1.src q.1.dst = true → Γ.sameAtom p.1.src p.1.dst = false → Γ.sameAtom q.1.src q.1.dst = false →
        ∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt (Γ.BAScost_trB p q) k a b

/-- How L3d2 reads target 3 (not binding; 1152 :189-191, T2448 audit O1): at the outputs of any lists with `BALocRegConcl`, the premises
`P.g.nM ≤ p` and `(BAShadowPG P).LocReg345 p` of `baAuxNested_holds` (`BAAtom2:647`), `BAAnpAux` (`:677`), `BAAnpAuxG` (`BAAuxGraph2B:865`). -/
example : Prop :=
  T2469_ConclUpto5 → ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))), BALocRegConcl p c K0 d D outs errs →
    ∀ Q ∈ outs, Q.g.nM ≤ p ∧ (BAShadowPG Q).LocReg345 p

/-- Target 4 (i)-(iv) data (not binding): the path invariant at the R1 witnesses and at the replacement `edge` witness, with an output of each moved
shape carrying it (`P_B` k = 1 and `P_A` k = 2 need hand-built families; `P_C` has `BALocReg1Inst.pathInv2_C`; `baPEr` has `pathInv2_Er`). -/
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPB) ((baPG BASimInst.baPB).withinOutsT BASimInst.pB) ∧ (baPG BASimInst.baPB).img.PathInv2 1 ∧
    (∃ Q : BAPGraph (Fin 2), (BAShape.e2, Q) ∈ (baPG BASimInst.baPB).withinOutsT BASimInst.pB ∧ Q.img.PathInv2 1) ∧
    ∃ Q : BAPGraph (Fin 2), (BAShape.macroA, Q) ∈ (baPG BASimInst.baPB).withinOutsT BASimInst.pB ∧ Q.img.PathInv2 1
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPC) ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0) ∧ (baPG BASimInst.baPC).img.PathInv2 2 ∧
    (∃ Q : BAPGraph (Fin 2), (BAShape.e2, Q) ∈ (baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0 ∧ Q.img.PathInv2 2) ∧
    ∃ Q : BAPGraph (Fin 2), (BAShape.macroB, Q) ∈ (baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0 ∧ Q.img.PathInv2 2
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPA) BASimInst.ggFT ∧ (baPG BASimInst.baPA).img.PathInv2 2 ∧
    ∃ Q : BAPGraph (Fin 2), (BAShape.e2, Q) ∈ BASimInst.ggFT ∧ Q.img.PathInv2 2
example : Prop := ∃ Q : BAPGraph (Fin 2), (BAShape.e2, Q) ∈ BALocReg1Inst.outsEr ∧ Q.img.PathInv2 1

/-- Target 4 (vi) (not binding): target 2 at a locally standard graph reached from a `p = 2` start term (no start term is locally standard), with no
hypothesis (the graph of `BALocReg1B_reach_locStd`). -/
example : Prop :=
  ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, ∃ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q ∧ ¬ P0.g.LocStd ∧ Q.g.LocStd ∧
    Q.g.nM = 1 ∧ PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2

/-- Target 4 (vii) (not binding): target 3 (c) at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10`, with the identity at the flow point of
`BAEngineInst` (`d = 3`, `L = 4`, `W = 2`, `ℓ0`); no hypothesis. -/
example : Prop :=
  ∃ outs errs : List (BAPGraph (Fin 2)), BALocRegConcl 2 (1 / 4) 2 3 10 outs errs ∧
    (∀ Q ∈ outs, Q.g.LocStd ∧ Q.g.nM ≤ 2 ∧ PGraph.LocReg345 Q.img 2 ∧ (BAShadowPG Q).LocReg345 2) ∧
    ∫ ω, (BAGraph.ofLGraph (fxyPowGraph 2)).val
        (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
        BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, BAComb.val (outs ++ errs)
        (BAlwData 3 4 2 RBM.BA.CouplingWindowInst.g0P RBM.BA.CouplingWindowInst.EP RBM.BA.CouplingWindowInst.t0P RBM.BA.CouplingWindowInst.m0P ω)
        BASymm1Inst.ℓ0 ∂(PF 3 4 2 0)
