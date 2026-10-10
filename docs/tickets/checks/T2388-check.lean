/-
Release check for T2388 (dispatcher V2, Sat Oct 10 12:46 UTC 2026; DECISIONS §199).  BA-E1: the block Anderson evolution kernel,
the five stage-E pins, `lem:sum_Ndecay` at BA and the BA `Ξ` bounds (new `BA/EKPins.lean`).  Merged names only.
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2388-check.lean
-/
import RBM3D.BA.Prop6Path
import RBM3D.BA.KKernel
import RBM3D.BA.KBase
import RBM3D.Evolution.Pins
import RBM3D.Evolution.XiPins

#check @RBM.BA.BAMss
#check @RBM.BA.BAMB
#check @RBM.BA.BATheta
#check @RBM.BA.BAReal
#check @RBM.BA.BATheta_resolvent
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.BAMss_norm_eq_BAK
#check @RBM.BA.BAProp5
#check @RBM.BA.baProp5_holds
#check @RBM.BA.baProp5to8_holds
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.zeroModeSet
#check @RBM.ellT
#check @RBM.EKSumNdecay
#check @RBM.ekSumNdecay_holds
#check @RBM.EKXiDecay
#check @RBM.EKXiBall
#check @RBM.EKSameRow
