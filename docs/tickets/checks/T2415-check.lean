/-
Release check for T2415 (dispatcher V2, Sun Oct 11 09:03 UTC 2026; DECISIONS §229).  BA-T T8-BA: the BA Step 2 carrier
(supervisor 0853 REQ-BAT Q1, BAT-C1).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2415-check.lean
-/
import RBM3D.BA.FlowPins
import RBM3D.Chain.Step2Gen
import RBM3D.BA.ImmLower

#check @RBM.BA.Step2Mat
#check @RBM.BA.Step2Data
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.bandStep2Data
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAStep2
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BALloop
#check @RBM.BA.BAGt
#check @RBM.BA.BAMfine
#check @RBM.BA.BAKsol
#check @RBM.BA.BAKloop
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BAdom
#check @RBM.BA.BAm_im_lower
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.Sizes.seqHflowBA
