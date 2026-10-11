/-
Release check for T2413 (dispatcher V2, Sun Oct 11 08:58 UTC 2026; DECISIONS §228).  BA TL-D: design of stage TL
(supervisor 0853 REQ-TLS, TL-C1 to TL-C4), report only.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2413-check.lean
-/
import RBM3D.BA.FlowPins
import RBM3D.BA.LWPinsBA
import RBM3D.BA.KSolve
import RBM3D.BA.EKPins
import RBM3D.BA.Step1Boot

#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.STLKgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STKboundgL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAKsolve
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
#check @RBM.BA.BAReal
#check @RBM.BA.baEKXiDecay_holds
#check @RBM.BA.baEKXiBall_holds
