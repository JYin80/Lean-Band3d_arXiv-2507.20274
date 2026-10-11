/-
Release check for T2406 (dispatcher V2, Sun Oct 11 03:20 UTC 2026; DECISIONS §219).  BA-E3: `lem:sum_decay_nonzero` at BA (new
`BA/EKNonzero.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2406-check.lean
-/
import RBM3D.BA.EKPins
import RBM3D.BA.EKSum
import RBM3D.BA.Prop6Path
import RBM3D.BA.KKernel
import RBM3D.Evolution.Nonzero

#check @RBM.BA.BAEKSumDecayNonzero
#check @RBM.BA.baEKSameRow_holds
#check @RBM.BA.BAEKSameRow
#check @RBM.BA.baProp8_holds
#check @RBM.BA.BAProp8
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.BAUN
#check @RBM.BA.BAuKer
#check @RBM.BA.BAuKer_eq_one_add_Xi
#check @RBM.BA.BAMss_norm_eq_BAK
#check @RBM.BA.BAK_row_sum
#check @RBM.zeroModeSet
#check @RBM.ekSumDecayNonzero_holds
#check @RBM.EKSumDecayNonzero
#check @RBM.norm_zeroModeSet_UN_le
#check @RBM.BA.EKPinsInst.inst_BAEKSumDecayNonzero
