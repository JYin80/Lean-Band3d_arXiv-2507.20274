/-
Release check for T2378 (dispatcher V2, Sat Oct 10 09:56 UTC 2026; DECISIONS §191).  BA-DGE: design of stages G (Green layer) and E (EK layer),
report only.  Merged names the design starts from.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2378-check.lean
-/
import RBM3D.BA.Step1Boot
import RBM3D.BA.GreenSchur
import RBM3D.Green.GbEXP
import RBM3D.Green.Pins
import RBM3D.Induction.Defs

#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAGt_sub_BAMfine
#check @RBM.Gauss.Sizes.STGbEXP
#check @RBM.Green.GbEXPV3Theorem
#check @RBM.Green.stGbEXP_holds
