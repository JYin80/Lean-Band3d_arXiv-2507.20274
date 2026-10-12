/-
Release check for T2452 (dispatcher V3, Mon Oct 12 12:24 UTC 2026; DECISIONS §264).  BA-U U-D: the C10 coverage census (by use) of sub-stage U and the five
unreleased ST-side T rows (supervisor 1152 U-C6 (a)-(d)), report only.  Merged names the census starts from.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2452-check.lean
-/
import RBM3D.Path.DifREP3
import RBM3D.Path.NetLift2
import RBM3D.Induction.Step2Scale
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.EMn2Exp1
import RBM3D.Induction.NQGood1
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.ContinuityNet
import RBM3D.Evolution.FarEntry
import RBM3D.Green.CondDom
import RBM3D.Chain.Step2Gen
import RBM3D.BA.TwistStep
import RBM3D.BA.EMn2BA
import RBM3D.BA.Prop6Path
import RBM3D.BA.Step1Setup

/-! ## T1's Step 2 pins and the skeleton that takes them (band) -/
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STGridMartAt
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STNetLift2
#check @RBM.Gauss.Sizes.STScaleExists
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.ST_step2_of_pins
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN
#check @RBM.Gauss.Sizes.stOptL2a_martingale
#check @RBM.Gauss.Sizes.stOptL2_of_pins

/-! ## `Path/DifREP1–3`: the band producers of the grid pins, and their inputs from U-row files -/
#check @RBM.Ind.stGridRepN_holds
#check @RBM.Ind.stGridMart_holds
#check @RBM.Ind.stGridMartAt_holds
#check @RBM.Ind.gridRepRemN_holds
#check @RBM.Ind.gridRepTailN_holds
#check @RBM.Ind.gridRepWTailN_holds
#check @RBM.Ind.difRep2_norm_STeeM_le_N
#check @RBM.Ind.difRep_flow_bounds
#check @RBM.Ind.norm_STeeM_shiftN_le
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.loopShiftErrN
#check @RBM.zeroModeSet_UN

/-! ## `Path/NetLift1–2` and `Step2Scale`: the band producers of `STNetLift2`, `STScaleExists`; the generic net -/
#check @RBM.Gauss.Sizes.stNetLift2_holds
#check @RBM.Gauss.Sizes.stNetLift2_part1
#check @RBM.Ind.Step2NetLift
#check @RBM.Ind.step2NetLift
#check @RBM.Gauss.Sizes.stScaleExists_holds
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Ind.ContinuityNet.cont_core

/-! ## The generic Step 2 pins over the carrier (`Chain/Step2Gen`) and the one kernel (U-C4) -/
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STGridRepNgL
#check @RBM.BA.STNetLift2gL
#check @RBM.BA.STScaleExistsgL
#check @RBM.BA.bandStep2_STGridMart
#check @RBM.BA.bandStep2_STGridRepN
#check @RBM.BA.bandFM_STNetLift2
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.FlowFM
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.BAflowT0

/-! ## Stage TL's BA reuse of `DifREP2` (the twisted grid martingale) -/
#check @RBM.BA.BATwistGridMartAt
#check @RBM.BA.BATwistGridMart
#check @RBM.BA.baTwistGridMart_holds
#check @RBM.BA.baTwistGridRem_holds
#check @RBM.BA.baTwistGridTail_holds
#check @RBM.BA.baTwistGridWTail_holds

/-! ## `Path/KellStar`: the band pin, its consumers, and T2-BA's inline far field with its copies -/
#check @RBM.Path.KellStarEv
#check @RBM.Path.kellStarEv
#check @RBM.Path.kellStarEv_instance
#check @RBM.prop5Decay_holds
#check @RBM.Gauss.Sizes.lemDecCalEPrec_kell
#check @RBM.Gauss.Sizes.STFarEntryAtLog
#check @RBM.Gauss.Sizes.stFarEntryAtLog
#check @RBM.Gauss.Sizes.emn2Exp_kellStar_far
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.BACompBound
#check @RBM.BA.baComp_holds
#check @RBM.BA.EMn2BA_bparam_le
#check @RBM.BA.baProp5_holds
#check @RBM.BA.baGopbound

/-! ## `Path/LemDecCalE*`: the case (iii) pin and its band producer -/
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.stLemDecCalE_holds

/-! ## `Green/CondDom`: the one fact the rows use, and two candidate model-free exports -/
#check @RBM.Green.etaT_le_of_le
#check @RBM.Green.condRowReal
#check @RBM.Green.perTimeDomAt_of_moment
