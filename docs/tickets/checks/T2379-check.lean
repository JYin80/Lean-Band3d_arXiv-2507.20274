/-
Release check for T2379 (dispatcher V2, Sat Oct 10 09:56 UTC 2026; DECISIONS §191).  BA-DT: design of stage T/U/V (the chain over the BA carrier),
report only.  Merged names the design starts from.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2379-check.lean
-/
import RBM3D.BA.FlowPins
import RBM3D.Induction.MainIndOut
import RBM3D.Induction.MainIndHolds

#check @RBM.BA.STMainIndG
#check @RBM.BA.STKboundgL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STMLOutG
#check @RBM.Gauss.Sizes.stMainInd_holds
#check @RBM.Gauss.Sizes.STMainInd
