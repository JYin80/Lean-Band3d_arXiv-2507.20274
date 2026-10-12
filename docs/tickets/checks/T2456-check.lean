/-
Release check for T2456 (dispatcher V3, Mon Oct 12 13:13 UTC 2026; DECISIONS §265).  BA-L L3b1 `BALocReg1`: the invariants (1)–(5) of `lem:localregular` along `BAReach`
(twin of the band `LocalRegular`, `LocalRegular2` under S′; supervisor 1152 O7), the path inputs `BAShapePath` of the BA-only shapes (0948 O2R-C4,
0951 L4-C4 (a)), `BASimP'` (0951 L4-C1), the start bound `P0.g.nM ≤ p` (DECISIONS §260 (1)), the `|f_{xy}|^p` value identity at BA.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2456_`; content binding; the 1b names them as the ticket proposes or as
the 1a fixes), the binder of split Σ, and shapes (not binding) of the tools, the bridge, the consumer reading and the instance data.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2456-check.lean
-/
import RBM3D.Graph.BAShapeO2B
import RBM3D.Graph.BAShapeO2
import RBM3D.Graph.BAEngine
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BALvl1C
import RBM3D.Graph.BALvl1B
import RBM3D.Graph.BALvl1B2
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BAScost
import RBM3D.Graph.BAScost2
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BASymm2
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAAtomic2
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.LocalRegular
import RBM3D.Graph.LocalRegular2
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LWEngine
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes

set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open RBM RBM.Gauss RBM.Graph

/-! ## Part 1: merged names -/
-- the band invariant (`LocalRegular`, `LocalRegular2`): the predicates (1)-(5), the coloured path invariant, its step, start, and (3)-(5) at `LocStd`
#check @RBM.Graph.PGraph.LocReg1
#check @RBM.Graph.PGraph.LocReg2
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.PGraph.LocReg6
#check @RBM.Graph.PGraph.PathInv2
#check @RBM.Graph.LGraph.localReg2_PathFam
#check @RBM.Graph.localReg2_Fam
#check @RBM.Graph.localReg2_Fam.map
#check @RBM.Graph.localReg2_Fam.flip
#check @RBM.Graph.localReg2_Fam.of_add_diag
#check @RBM.Graph.localReg2_twistG_cendsMS
#check @RBM.Graph.localReg_lwSymmTwistG_molGraph
#check @RBM.Graph.LGraph.localReg2_pathFam_map
#check @RBM.Graph.LGraph.localReg2_pathFam_partition
#check @RBM.Graph.localReg2_pathFam_owxT1
#check @RBM.Graph.localReg2_pathFam_oe2xR8
#check @RBM.Graph.pathInv2_locStep
#check @RBM.Graph.fxyPowGraph_pathInv2
#check @RBM.Graph.PGraph.PathInv2.locReg345
#check @RBM.Graph.LGraph.molNV_le_molNW_add_one
#check @RBM.Graph.lw_localregular_upto5
#check @RBM.Graph.localReg2_inst_Q_locReg345
#check @RBM.Graph.fxyPowGraph
#check @RBM.Graph.fxyPowGraph_nM
#check @RBM.Graph.fxyPowGraph_counters
#check @RBM.Graph.localReg_fxy_mem_dotted
#check @RBM.Graph.fxyPowGraph_val_eq
#check @RBM.Graph.lw_fxyPow_integral_eq
#check @RBM.Graph.fxyVal
#check @RBM.Graph.LocStep
#check @RBM.Graph.LWLocRegConcl
-- R0 (`BAAtomic`, `BAAtomic2`): the atomic image, its normality, counters, molecules, local standardness; the lift and `BAPathLift`
#check @RBM.Graph.promoteC
#check @RBM.Graph.atomSetoid
#check @RBM.Graph.BAGraph.img
#check @RBM.Graph.BAPGraph.img
#check @RBM.Graph.BAGraph.img_normal
#check @RBM.Graph.BAGraph.img_counters
#check @RBM.Graph.BAGraph.img_molOf_eq_iff
#check @RBM.Graph.BAGraph.img_locStd_iff
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.baPG
#check @RBM.Graph.liftC
#check @RBM.Graph.BAPathLift
#check @RBM.Graph.BAPathLift_holds
#check @RBM.Graph.BAAtomic_pathFam_iff
-- L3c1 (`BAAtom`, `BAAtom2`, `BAAuxGraph2B`): the shadow and the merged consumers of (3)-(5) and `n_M ≤ p`
#check @RBM.Graph.BAGraph.shadow
#check @RBM.Graph.BAShadowPG
#check @RBM.Graph.BAGraph.shadow_mol
#check @RBM.Graph.BAGraph.shadow_nM
#check @RBM.Graph.BAAtom_shadow_molOf_eq_iff
#check @RBM.Graph.baAuxNested_holds
#check @RBM.Graph.BAAnpAux
#check @RBM.Graph.BAAnpAuxG
-- R1 (`BASim`, `BASim3`): the tagged frame step, its outputs, the matching, relabelling, the twist, the witness steps
#check @RBM.Graph.BAFrameStepT
#check @RBM.Graph.BAFrameStepT.weight
#check @RBM.Graph.BAFrameStepT.within
#check @RBM.Graph.BAFrameStepT.edge
#check @RBM.Graph.BAFrameStepT.gg
#check @RBM.Graph.BAFrameStepT.ggSplit
#check @RBM.Graph.BAPGraph.outsT
#check @RBM.Graph.BAPGraph.withinOutsT
#check @RBM.Graph.BAPGraph.splitOutsT
#check @RBM.Graph.BAGraph.tagStd
#check @RBM.Graph.BAGraph.tagT1
#check @RBM.Graph.BAGraph.extraB
#check @RBM.Graph.BASim_mem_outsT
#check @RBM.Graph.BAMatch
#check @RBM.Graph.baMatch_holds
#check @RBM.Graph.PGraph.BAEquiv
#check @RBM.Graph.PGraph.BAEquivC
#check @RBM.Graph.PGraph.BASim_BAEquiv_toC
#check @RBM.Graph.BAPGraph.twist
#check @RBM.Graph.BAPGraph.BASim_outOf
#check @RBM.Graph.BASim_outOf_baInv
#check @RBM.Graph.BASimInst.baPA
#check @RBM.Graph.BASimInst.baPB
#check @RBM.Graph.BASimInst.pB
#check @RBM.Graph.BASimInst.baPC
#check @RBM.Graph.BASimInst.pC
#check @RBM.Graph.BASimInst.qC
#check @RBM.Graph.BASimInst.baPE
#check @RBM.Graph.BASimInst.pE
#check @RBM.Graph.BASimInst.ggFT
#check @RBM.Graph.BASimInst.hTA
#check @RBM.Graph.BASimInst.hTB
#check @RBM.Graph.BASimInst.hTC
#check @RBM.Graph.BASimInst.hTE
#check @RBM.Graph.BASimInst.tag_exists
#check @RBM.Graph.ba_twist_inv_out
-- L3b3′, L3b4′, L3b4″ (`BAScost`, `BAStepS`, `BAShapeO2B`): shapes, tagged steps, the cost twins of targets 1-3, reachability, the transfer graphs
#check @RBM.Graph.BAShape
#check @RBM.Graph.BTStep
#check @RBM.Graph.untag
#check @RBM.Graph.BReach
#check @RBM.Graph.BReach.ind
#check @RBM.Graph.BAShapeLL
#check @RBM.Graph.BAFrameStepTN
#check @RBM.Graph.BALocStepT
#check @RBM.Graph.BASimC'
#check @RBM.Graph.baSimC'_holds
#check @RBM.Graph.baEquivCost_holds
#check @RBM.Graph.baCostTwist_holds
#check @RBM.Graph.baShapeLL_twist
#check @RBM.Graph.baShapeLL_s1_tn
#check @RBM.Graph.baShapeLL_e1_tn
#check @RBM.Graph.baUntag_locStepT
#check @RBM.Graph.baNormal_locStepT
#check @RBM.Graph.baReach_bReach
#check @RBM.Graph.baShapeLL_e2_tn
#check @RBM.Graph.baShapeLL_macroA_tn
#check @RBM.Graph.baShapeLL_macroB_tn
#check @RBM.Graph.baLocReg6_holds
#check @RBM.Graph.BAShapeO2B_ext_normal
#check @RBM.Graph.BAShapeO2B_lwSplit_last
#check @RBM.Graph.BAGraph.BAScost_trA
#check @RBM.Graph.BAGraph.BAScost_trB
#check @RBM.Graph.BAScost_pack
-- L3a3-L3a5 (`BALvl1A`, `BALvl1B`, `BALvl1B2`, `BALvl1C`): the step, reachability, goodness (`n_M` per step), coarsening, induction
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BALvl1A_reach_refl
#check @RBM.Graph.BALvl1AInst.locStepB
#check @RBM.Graph.BALvl1Good
#check @RBM.Graph.BAlvl1StepGood
#check @RBM.Graph.baLvl1StepGood_holds
#check @RBM.Graph.BALvl1B_adj_mono
#check @RBM.Graph.BALvl1B_coarse
#check @RBM.Graph.BALvl1B_splitG_struct
#check @RBM.Graph.ba_lvl1_induction
#check @RBM.Graph.BAReach.trans
-- L3d3 (`BAEngine`): the conclusion L3d2 reads with target 7, the engine, the `LocStd` producer
#check @RBM.Graph.BALocRegConcl
#check @RBM.Graph.baEngine_assemble
#check @RBM.Graph.ba_localregularX
#check @RBM.Graph.BAEngine_pL_locStd
-- vocabulary and data (`BAVocab`, `BAExpandW`, `FineModel`, `Sizes`)
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.ofLGraph
#check @RBM.Graph.BAGraph.counters_ofLGraph
#check @RBM.Graph.BAGraph.val_ofLGraph
#check @RBM.Graph.BALData.toLData
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
#check @RBM.Gauss.Idx

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- Target 3 (a) (`baShapePath_s1_tn : BAShapePath BAShape.s1 BAFrameStepTN`; `BAShapePath` = `t/T2397` probe 174 with `img P` → `P.img`): vacuous. -/
def T2456_S1Path : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (BAShape.s1, Q) ∈ LT →
    ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- Target 3 (b) (`baShapePath_e1_tn`): the `e1` outputs (the `tagT1` outputs of `lanlwT1` in `edge`, `ggSplit`). -/
def T2456_E1Path : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (BAShape.e1, Q) ∈ LT →
    ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- Target 3 (c) (`baShapePath_e2_tn`; 0948 O2R-C4). -/
def T2456_E2Path : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (BAShape.e2, Q) ∈ LT →
    ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- Target 3 (d) (`baShapePath_macroA_tn`; 0948 O2R-C4): stage 2 of `within`. -/
def T2456_MacroAPath : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (BAShape.macroA, Q) ∈ LT →
    ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- Target 3 (e) (`baShapePath_macroB_tn`; 0948 O2R-C4): stage 1 `d2`-`d4` and stage 2 of `ggSplit`. -/
def T2456_MacroBPath : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (BAShape.macroB, Q) ∈ LT →
    ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- The binder of split Σ (used only if the dispatcher signs Σ off before 1b): targets 3 (c)-(e), the form `∀ sh, … → BAShapePath sh BAFrameStepTN`. -/
def T2456_PathBinder : Prop :=
  ∀ sh : BAShape, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB →
    ∀ (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BAFrameStepTN P LT → ∀ Q : BAPGraph (Fin 2), (sh, Q) ∈ LT →
      ∀ k : ℕ, P.img.PathInv2 k → Q.img.PathInv2 k

/-- Target 2 (`baSimP'_holds m : BASimP' m BALocStepT`; 0951 L4-C1): the band step per output, as `BASimC'` (`BAStepS:84`). -/
def T2456_SimP : Prop :=
  ∀ (m : ℂ) (P : BAPGraph (Fin 2)) (LT : List (BAShape × BAPGraph (Fin 2))), BALocStepT P LT →
    ∃ P' : PGraph (Fin 2), (∀ k : ℕ, P.img.PathInv2 k → P'.PathInv2 k) ∧
      ∀ Q : BAPGraph (Fin 2), (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧
        ∃ R ∈ L', ∀ k : ℕ, R.PathInv2 k → Q.img.PathInv2 k

/-- Target 4 (`baPathStep_holds : BAPathStep (untag BALocStepT)`; probe 159 with `img` → `BAPGraph.img`). -/
def T2456_PathStep : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), untag BALocStepT P L →
    ∀ k : ℕ, P.img.PathInv2 k → ∀ Q ∈ L, Q.img.PathInv2 k

/-- Target 5 (`baPathInit_holds : ∀ p, BAPathInit p`; probe 155): the path invariant at the image of every start term. -/
def T2456_PathInit : Prop :=
  ∀ p : ℕ, ∀ P ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P.img.PathInv2 p

/-- Target 6 (`baStart_nM_le`; DECISIONS §260 (1)): the start bound. -/
def T2456_StartNM : Prop :=
  ∀ p : ℕ, ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P0.g.nM ≤ p

/-- Target 7 (`def BALocReg15 : Prop` with this body, and `baLocReg15_holds : BALocReg15`; supervisor 1152 O7): (1)-(5) along `BAReach` from a start
term, in the form L3d2 reads: the path invariant at the image; (2) `n_M ≤ p` and `LocReg2` on the image (atoms, `T2397c`); at `LocStd`: (1) on the
image, (3)-(5) on the image and on the shadow (the form of `baAuxNested_holds`, `BAAnpAux`, `BAAnpAuxG`). -/
def T2456_LocReg15 : Prop :=
  ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition →
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q →
      Q.img.PathInv2 p ∧ Q.g.nM ≤ p ∧ PGraph.LocReg2 Q.img p ∧
        (Q.g.LocStd → PGraph.LocReg1 Q.img ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p)

/-- Target 9 (`ba_fxyPow_integral_eq`; twin of `lw_fxyPow_integral_eq`, `LocalRegular:2036`): the start graph has the value `|f_{xy}|^p` at `BAlwData`. -/
def T2456_ValueId : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) (p : ℕ), Even p → ∀ ℓe : Fin 2 → Idx d L W,
    ∫ ω, (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1) ^ (p / 2) *
        star (fxyVal (BAlwData d L W g0 Em t m ω).toLData (ℓe 0) (ℓe 1)) ^ (p / 2) ∂(PF d L W 0)

/-- Statement level (not binding): the three O2R-C4 shapes give the binder; with the band half and the closed shapes they give the step; the step, the
start and the start bound give the contract; under Σ the binder gives the contract. -/
example : Prop := T2456_E2Path → T2456_MacroAPath → T2456_MacroBPath → T2456_PathBinder
example : Prop := T2456_SimP → T2456_S1Path → T2456_E1Path → T2456_PathBinder → T2456_PathStep
example : Prop := T2456_PathInit → T2456_PathStep → T2456_StartNM → T2456_LocReg15
example : Prop := T2456_PathBinder → T2456_LocReg15

/-- How L3d2 reads target 7 (not binding; 1152 O7, T2448 audit O1): `BALocRegConcl` (a) gives `LocStd`, (c) the start term and `BAReach`; target 7
there gives the premises `P.g.nM ≤ p`, `(BAShadowPG P).LocReg345 p` of `baAuxNested_holds` (`BAAtom2:647`), `BAAnpAux` (`:677`), `BAAnpAuxG`
(`BAAuxGraph2B:865`). -/
example : Prop :=
  T2456_LocReg15 → ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))), BALocRegConcl p c K0 d D outs errs →
    ∀ Q ∈ outs, Q.g.nM ≤ p ∧ PGraph.LocReg345 Q.img p ∧ (BAShadowPG Q).LocReg345 p

/-- Target 1 shapes (not binding; the 1a may add `P.g.Normal`): the twist, and R1's relabelling `BAEquivC`. -/
example : Prop := ∀ (c t : Bool) (P : BAPGraph (Fin 2)) (k : ℕ), (P.twist c t).img.PathInv2 k ↔ P.img.PathInv2 k
example : Prop := ∀ (R S : PGraph (Fin 2)), R.BAEquivC S → ∀ k : ℕ, (R.PathInv2 k ↔ S.PathInv2 k)

/-- Target 8 shape (not binding): (3)-(5) on the image give (3)-(5) on the shadow (molecules: `BAGraph.img_molOf_eq_iff`, `BAGraph.shadow_mol`). -/
example : Prop := ∀ (Q : BAPGraph (Fin 2)) (p : ℕ), Q.g.Normal → PGraph.LocReg345 Q.img p → (BAShadowPG Q).LocReg345 p

/-- Target 10 (i)-(iv) data (not binding): the R1 witness steps as `BAFrameStepTN` steps, with the tags target 3 reads. -/
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPB) ((baPG BASimInst.baPB).withinOutsT BASimInst.pB) ∧
    BAShape.e2 ∈ ((baPG BASimInst.baPB).withinOutsT BASimInst.pB).map Prod.fst ∧
    BAShape.macroA ∈ ((baPG BASimInst.baPB).withinOutsT BASimInst.pB).map Prod.fst
example : Prop :=
  BAFrameStepTN (baPG BASimInst.baPC) ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0) ∧
    BAShape.e1 ∈ ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0).map Prod.fst ∧
    BAShape.e2 ∈ ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0).map Prod.fst ∧
    BAShape.macroB ∈ ((baPG BASimInst.baPC).splitOutsT BASimInst.pC BASimInst.qC 0).map Prod.fst
example : Prop := BAFrameStepTN (baPG BASimInst.baPA) BASimInst.ggFT ∧ BAShape.e2 ∈ BASimInst.ggFT.map Prod.fst

/-- Target 10 (vi) (not binding): targets 5-7 at `p = 2` from a start term. -/
example : Prop :=
  ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph 2)).partition, P0.g.nM ≤ 2 ∧ P0.img.PathInv2 2 ∧
    ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → Q.img.PathInv2 2 ∧ Q.g.nM ≤ 2
