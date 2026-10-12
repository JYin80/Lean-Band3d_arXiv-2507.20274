/-
Release check for T2436 (dispatcher V3, Mon Oct 12 01:08 UTC 2026; DECISIONS §245).  BA-TL TL1b: the bootstrap of T.7 Steps 5–6
(S1), `BATwistAvgProd`.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2436-check.lean
-/
import RBM3D.BA.TwistAvgA2
import RBM3D.Chain.Carrier

#check @RBM.BA.BATwistAvgProd
#check @RBM.BA.BATwistAvgLaw
#check @RBM.BA.BATwistAvgRec
#check @RBM.BA.baTwistAvgRec_holds
#check @RBM.BA.twAvgReg
#check @RBM.BA.twAvgReg_holds
#check @RBM.BA.twAvgX
#check @RBM.BA.twAvgXmax
#check @RBM.BA.twAvgT6_holds
#check @RBM.BA.T2427_TL1b
#check @RBM.BA.PrecL

namespace RBM.BA.T2436Check
/-- Target 2 as a Prop value. -/
example : Prop := ∀ d, RBM.BA.BATwistAvgProd d
/-- Target 1 is the merged interface. -/
example : Prop := RBM.BA.T2427_TL1b ↔ ∀ d, RBM.BA.BATwistAvgRec d → RBM.BA.BATwistAvgProd d
end RBM.BA.T2436Check
