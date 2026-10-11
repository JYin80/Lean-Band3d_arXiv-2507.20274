/-
Release check for T2411 (dispatcher V2, Sun Oct 11 07:42 UTC 2026; DECISIONS §223).  BA-G5b: conditional means, threshold families, family moment bound
(R6), and the owed pins BAFamGain, BAFAav (new `BA/GreenCond*.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2411-check.lean
-/
import RBM3D.BA.GreenMinor3
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenLDE
import RBM3D.Green.MinorDiffCond
import RBM3D.Green.FlucIterGain

#check @RBM.BA.BAFamGain
#check @RBM.BA.BAFAav
#check @RBM.BA.GreenMinor_famGain
#check @RBM.BA.GreenMinor_Tower
#check @RBM.BA.baStab_holds
#check @RBM.BA.baLDEin_holds
#check @RBM.BA.BAGiiGEX
#check @RBM.Green.badTower
#check @RBM.Green.meas_badTower_le
