/-
Release check for T2403 (dispatcher V2, Sun Oct 11 01:01 UTC 2026; DECISIONS §215).  BA-G4: the off-diagonal decay (D3.4) and the
pin `BAGbEXPij'` (new `BA/GreenOff.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2403-check.lean
-/
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.GreenLDE

#check @RBM.BA.BAGbEXPij'
#check @RBM.BA.BAStab
#check @RBM.BA.GreenCore_Xstar
#check @RBM.BA.GreenCore_Xi
#check @RBM.BA.GreenCore_coupled
#check @RBM.BA.GreenCore_diag
#check @RBM.BA.GreenCore_carrier
#check @RBM.BA.GreenCore_decayConcl
#check @RBM.BA.GreenCore_loopPrem
#check @RBM.BA.baStab_of_real
#check @RBM.BA.baM_rhohat
#check @RBM.BA.baMfine_rhohat
#check @RBM.BA.baTheta_weighted_l1
#check @RBM.BA.GreenStab_clam
#check @RBM.BA.GreenStab_CTheta
#check @RBM.BA.baLDEin_holds
