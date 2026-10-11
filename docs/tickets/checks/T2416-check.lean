/-
Release check for T2416 (dispatcher V2, Sun Oct 11 09:04 UTC 2026; DECISIONS §229).  BA-T T2-BA: lem:EMn2_N at BA with
T6-BA (supervisor 0853 REQ-BAT Q1, Q2, BAT-C2).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2416-check.lean
-/
import RBM3D.Induction.EMn2Exp2
import RBM3D.Induction.Contract
import RBM3D.BA.FlowPins
import RBM3D.BA.KSolve
import RBM3D.BA.Prop6Path
import RBM3D.BA.GreenStab
import RBM3D.BA.KKernel
import RBM3D.BA.GreenSchur
import RBM3D.BA.Ward

#check @RBM.Gauss.Sizes.emn2PolyFacts
#check @RBM.Gauss.Sizes.emn2ExpFacts
#check @RBM.Gauss.Sizes.emn2ExpHK
#check @RBM.Gauss.Sizes.emn2ExpEllStar
#check @RBM.Gauss.Sizes.stEMn2PolygL_of
#check @RBM.Gauss.Sizes.stEMn2ExpJgL_of
#check @RBM.Gauss.Sizes.stEMn2ExpgL_of
#check @RBM.BA.STEMn2PolygL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.Gauss.Sizes.STContractM
#check @RBM.Gauss.Sizes.stContractM_holds
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.ztOf
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAKsolve
#check @RBM.BA.baK_unique
#check @RBM.BA.BAProp5
#check @RBM.BA.baProp5_holds
#check @RBM.BA.baTheta_weighted_l1
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAPropM
#check @RBM.BA.BAt0_lt_one
#check @RBM.SB
