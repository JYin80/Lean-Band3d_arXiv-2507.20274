/-
Release check for T2414 (dispatcher V2, Sun Oct 11 08:59 UTC 2026; DECISIONS §228).  BA-T T8b: the generic drift kernel
of Step 2 (supervisor 0853 BAT-F1 (a)-(e), BAT-F2).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2414-check.lean
-/
import RBM3D.Chain.NewKLKGen
import RBM3D.BA.FlowPins
import RBM3D.BA.KSolve
import RBM3D.BA.EKPins
import RBM3D.Induction.NewKLK
import RBM3D.Induction.Step2K2

#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.STmsigg
#check @RBM.BA.STthetaOpg
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.STgDriftg
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STK2decaygL
#check @RBM.BA.NewKLKGenHyp
#check @RBM.BA.stNewKLKAtgL'_of
#check @RBM.BA.bandStep2_STNewKLK
#check @RBM.BA.baFMz
#check @RBM.BA.BAKsolve
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
#check @RBM.BA.BAUN
-- G1: the band statements stay as merged.
example (d : ℕ) : RBM.Gauss.Sizes.STNewKLK d := RBM.Gauss.Sizes.stNewKLK_holds d
example (d : ℕ) : RBM.Gauss.Sizes.STK2decay d := RBM.Gauss.Sizes.stK2decay_holds d
