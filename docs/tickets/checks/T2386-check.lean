/-
Release check for T2386 (dispatcher V2, Sat Oct 10 12:39 UTC 2026; DECISIONS §198).  BA-T T8: the Step 2 vocabulary over the carrier
(new `Chain/Step2Gen.lean`), `bandFM` moved into `Chain/Carrier.lean`, `Induction/LocalAvg1.lean` and `LocalAvg2.lean` restated in place.
Part 1: the carrier and the band instance (they keep their full names in `RBM.BA`).  Part 2: the `Step2Defs` vocabulary (not edited).
Part 3 (G1): the band statements of `LocalAvg1/2` that must stay unchanged; the auditor adds `example : <statement> := <name>` for each.
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2386-check.lean
-/
import RBM3D.BA.FlowPins
import RBM3D.Induction.LocalAvg2

/-! ## Part 1: carrier, band instance -/
#check @RBM.BA.FlowFM
#check @RBM.BA.bandFM
#check @RBM.BA.baFMz
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.STLKgL

/-! ## Part 2: the vocabulary the generic forms read (`Step2Defs`, `Step34Pins`: unchanged) -/
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STJhatM
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STStep2
#check @RBM.Gauss.Sizes.STStep2LocalPT
#check @RBM.Gauss.Sizes.STStep2AvgPT
#check @RBM.Gauss.Sizes.STInitialGT2
#check @RBM.Gauss.Sizes.STL2decayPT
#check @RBM.Gauss.Sizes.STLocalAvgOfL2
#check @RBM.Gauss.Sizes.STOptL2
#check @RBM.Gauss.Sizes.STLWB
#check @RBM.Gauss.Sizes.STLWT
#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE

/-! ## Part 3 (G1): `LocalAvg1/2` band statements that stay -/
#check @RBM.Gauss.Sizes.stLocalPsi
#check @RBM.Gauss.Sizes.stInitialGT2_of_L2decay
#check @RBM.Gauss.Sizes.stStep2AvgPT_of_L2decay
#check @RBM.Gauss.Sizes.stStep2LocalPT_of_L2decay
#check @RBM.Gauss.Sizes.stLocalAvgOfL2_holds
