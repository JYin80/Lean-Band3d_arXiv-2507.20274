/-
Release check for T2393 (dispatcher V2, Sat Oct 10 21:21 UTC 2026; DECISIONS §205).  BA-T T6: the contraction inequality over any
Hermitian matrix (`Induction/Contract.lean` in place).  G1: the band pins below stay unchanged; the auditor adds
`example : <statement> := <name>` for each.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2393-check.lean
-/
import RBM3D.Induction.Contract
import RBM3D.Induction.ContractPt

#check @RBM.Gauss.Sizes.STContract
#check @RBM.Gauss.Sizes.stContract_holds
#check @RBM.Gauss.Sizes.STContractPt
#check @RBM.Gauss.Sizes.stContractPt_holds
#check @RBM.Gauss.Sizes.STLI
#check @RBM.Gauss.Sizes.STmaxL
#check @RBM.Gauss.loopFine
