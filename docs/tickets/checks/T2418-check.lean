/-
Release check for T2418 (dispatcher V2, Sun Oct 11 09:59 UTC 2026; DECISIONS §232).  BA-L L4a `BAExp14a`: S1 families,
kernels, ties, fine Ward (supervisor 0951 Q2, L4-C6).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2418-check.lean
-/
import RBM3D.Graph.LWExpTerm4
import RBM3D.Chain.LWGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.KBound
import RBM3D.BA.GreenSchur
import RBM3D.Induction.ScaleFacts

#check @RBM.Gauss.Sizes.lwExpTerm4_kerSum
#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.BA.LWcutg
#check @RBM.BA.LWEg
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.baKBoundAt_holds
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMB_row_l1
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.BA.baFMz
