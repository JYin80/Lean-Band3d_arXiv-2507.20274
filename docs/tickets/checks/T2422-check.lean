/-
Release check for T2422 (dispatcher V2, Sun Oct 11 10:30 UTC 2026; DECISIONS §234).  BA-G G6b: (GavLGEX) at BA by
composition (G6a wiring + G5b `BAFAav`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2422-check.lean
-/
import RBM3D.BA.GreenLocal
import RBM3D.BA.GreenCond2
import RBM3D.BA.Step1Boot

#check @RBM.BA.BAGbEXPav
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.baGbEXPii_holds
#check @RBM.BA.GreenLocal_FAav
#check @RBM.BA.GreenLocal_Wiring
#check @RBM.BA.greenLocal_gbEXPav_of_fa
#check @RBM.BA.BAFAav
#check @RBM.BA.baFAav_holds
#check @RBM.BA.STInitialGT2gL
