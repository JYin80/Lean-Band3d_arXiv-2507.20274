/-
Release check for T2399 (dispatcher V2, Sat Oct 10 22:57 UTC 2026; DECISIONS §212).  BA-K12: `BAKBoundAt` for every `n`,
`BAKbound`, the Ward carrier form `STKwardgL` and `BAKward` (new `BA/KBound.lean`; pin in `Chain/Carrier.lean`).
Merged names only.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2399-check.lean
-/
import RBM3D.BA.KStep
import RBM3D.BA.KWardIneq
import RBM3D.BA.KTreeRep
import RBM3D.BA.Prop6Path
import RBM3D.Loop.KLFinal
import RBM3D.Chain.Step2Gen

#check @RBM.BA.BAKBoundAt
#check @RBM.BA.BAKpiBoundAt
#check @RBM.BA.baKpiBoundAt_holds
#check @RBM.BA.baKsol_one
#check @RBM.BA.baKsol_two
#check @RBM.BA.baKsol_three
#check @RBM.BA.baWardIneq_holds
#check @RBM.BA.BAWardIneqAt
#check @RBM.BA.baKsolve
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.STKboundgL
#check @RBM.BA.baFMz
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Loop.KLbound_holds
#check @RBM.Loop.KLInduct_BoundAt_of_Kpi
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow
