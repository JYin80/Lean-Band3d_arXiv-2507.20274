/-
Release check for T2390 (dispatcher V2, Sat Oct 10 13:01 UTC 2026; DECISIONS §201).  BA-G3a: design gate for G3a, G3b, G4
(supervisor 1155 C1–C3), then the BA entrywise layer (new `BA/GreenCore.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2390-check.lean
-/
import RBM3D.BA.Step1Fam
import RBM3D.BA.Step1
import RBM3D.BA.GreenSchur
import RBM3D.BA.Ward
import RBM3D.BA.Prop5Short
import RBM3D.BA.CombesThomas
import RBM3D.Green.EntryCore
import RBM3D.Green.Stability

#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.BAGbEXPav
#check @RBM.BA.BAGiiGEX
#check @RBM.BA.BAGijGEX
#check @RBM.BA.baBootstrap'_holds
#check @RBM.BA.baStep1_holds
#check @RBM.BA.BAGt_sub_BAMfine
#check @RBM.BA.green_diag_split
#check @RBM.BA.green_off_split
#check @RBM.BA.BAPsiI_inBlock
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAoffDiag_scalar
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAMB_decay_large
#check @RBM.BA.BAMres_fine_apply
#check @RBM.Green.GoodEvent
#check @RBM.Green.Stable
#check @RBM.Green.Kstab3
