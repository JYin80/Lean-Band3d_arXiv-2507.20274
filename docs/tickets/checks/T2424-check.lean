/-
Release check for T2424 (dispatcher V2, Sun Oct 11 11:01 UTC 2026; DECISIONS §237).  BA-T T3-BA: lem:newKLK and the
K^(2) decay at BA (supervisor 0853 BAT-F1, BAT-F2).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2424-check.lean
-/
import RBM3D.Chain.NewKLKGen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step2BA
import RBM3D.BA.EMn2BA
import RBM3D.BA.KSolve
import RBM3D.BA.Prop6Path
import RBM3D.BA.Ward

#check @RBM.BA.NewKLKGenHyp
#check @RBM.BA.stNewKLKgL'_of
#check @RBM.BA.STNewKLKgL'
#check @RBM.BA.STK2decaygL'
#check @RBM.BA.baStep2Fam
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.BACompBound
#check @RBM.BA.baComp_holds
#check @RBM.BA.baProp5_holds
#check @RBM.BA.baK_unique
#check @RBM.BA.BAMB_diag_eq
#check @RBM.BA.BAMB_row_sq_real
