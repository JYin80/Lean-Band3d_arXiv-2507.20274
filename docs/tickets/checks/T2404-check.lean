/-
Release check for T2404 (dispatcher V2, Sun Oct 11 01:22 UTC 2026; DECISIONS §216).  BA-T T2: `lem: EMn2_N` over the carrier
(`Induction/EMn2Poly.lean`, `EMn2Exp1.lean`, `EMn2Exp2.lean` in place).  G1: the band pins below stay unchanged; the auditor adds
`example : <statement> := <name>` for each.  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2404-check.lean
-/
import RBM3D.Induction.EMn2Exp2
import RBM3D.Chain.Step2Gen
import RBM3D.Evolution.PropTInf
import RBM3D.BA.KSolve

#check @RBM.Gauss.Sizes.STEMn2Poly
#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Gauss.Sizes.stEMn2Poly_holds
#check @RBM.Gauss.Sizes.stEMn2Exp_holds
#check @RBM.BA.STEMn2PolygL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.BA.bandFM_STEMn2Poly
#check @RBM.BA.bandFM_STEMn2Exp
#check @RBM.BA.Step2Data
#check @RBM.BA.bandStep2Data
#check @RBM.BA.STJhatg
#check @RBM.BA.STEEg
#check @RBM.BA.STInitialGT2gL
#check @RBM.BA.STLWassmgL
#check @RBM.BA.STLWassmExpgL
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.emn2Exp_near
#check @RBM.Gauss.Sizes.emn2Exp_far12
#check @RBM.Gauss.Sizes.emn2Exp_far3
#check @RBM.Gauss.Sizes.emn2Exp_of_far3
#check @RBM.Gauss.Sizes.stContractPt_holds
#check @RBM.ekPropTInf_holds
#check @RBM.Loop.KLK_two
#check @RBM.BA.BAKsolve
