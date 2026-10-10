/-
Release check for T2402 (dispatcher V2, Sat Oct 10 23:12 UTC 2026; DECISIONS §213).  BA-G5c design gate (supervisor 2254 Q1, G1, G2).
Merged names only.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2402-check.lean
-/
import RBM3D.BA.GreenLDE
import RBM3D.BA.GreenSchur
import RBM3D.BA.Step1Boot
import RBM3D.Green.EntryCore
import RBM3D.Green.IBP
import RBM3D.Green.MinorDiff

#check @RBM.BA.BAGt_sub_BAMfine
#check @RBM.BA.green_diag_split
#check @RBM.BA.green_off_split
#check @RBM.BA.BAPsiI_inBlock
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.BAGbEXPii
#check @RBM.Green.GoodEvent
#check @RBM.BA.baLDEin_holds
#check @RBM.BA.BALDEin
