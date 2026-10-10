/-
Release check for T2400 (dispatcher V2, Sat Oct 10 22:57 UTC 2026; DECISIONS §212).  BA-G3b: the BA stability bound (the body of
`BAStab`, `K = 16 κ⁻⁴`) and the `M`, `Θ` row facts (new `BA/GreenStab.lean`).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2400-check.lean
-/
import RBM3D.BA.Prop5Short
import RBM3D.BA.Prop6Path
import RBM3D.BA.Ward
import RBM3D.BA.GreenSchur
import RBM3D.BA.CombesThomas

#check @RBM.BA.BAMss
#check @RBM.BA.BAMB
#check @RBM.BA.BAReal
#check @RBM.BA.BAMss_ss_diag
#check @RBM.BA.BAMss_row_offdiag_sum
#check @RBM.BA.BAoffDiag_scalar
#check @RBM.BA.BAMfine_row_l1
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAct_rate
#check @RBM.BA.BAp5s_rate
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.BATheta
