/-
Release check for T2408 (dispatcher V2, Sun Oct 11 04:32 UTC 2026; DECISIONS §222).  BA-G6a: the BA local law at a deterministic control, per-sequence
layer (new `BA/GreenLocal*.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2408-check.lean
-/
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.Step1Boot
import RBM3D.Green.LocalLaw

#check @RBM.BA.GreenCore_diag
#check @RBM.BA.GreenCore_decayConcl
#check @RBM.BA.GreenCore_loopPrem
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.baStab_holds
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.BAGiiGEX
#check @RBM.Green.LocalLawDetSeq
#check @RBM.Green.LocalLawDetThm
#check @RBM.Green.localLawDetThm
#check @RBM.Green.LoopFloorThm
#check @RBM.Green.loopFloorThm
#check @RBM.Green.avgBoundDetThm
#check @RBM.Green.gbEXPV3Theorem_of_parts
#check @RBM.Green.inv_Wd_le_maxLoopPM
