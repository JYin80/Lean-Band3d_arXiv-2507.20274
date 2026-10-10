/-
Release check for T2376 (dispatcher V2, Sat Oct 10 08:53 UTC 2026; DECISIONS §187).  BA-K06: `BA/KMolecule.lean`, the BA molecule layer
`K^{(π)}`, `Σ^{(π)}`, `(eq_K-Kpi)`, `(eq:molecule-Kpi)`, the factorisation at an innermost long edge, and the molecule weight
as an interface family.  No new pin here: the 1a fixes the statements (design gate) and the 1a-audit checks them.
Part 2: merged names the route reuses.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2376-check.lean
-/
import RBM3D.BA.KTreeRep
import RBM3D.Loop.KLSumZeroWard
import RBM3D.Loop.KLIndStepB

open RBM RBM.Loop RBM.BA

/-! ## Part 2: merged names -/
#check @RBM.BA.baTreeRep
#check @RBM.BA.baKsolve
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.BAGamma
#check @RBM.BA.BACactusVal
#check @RBM.BA.BACactusValLeafW
#check @RBM.BA.BACactusValEdgeW
#check @RBM.BA.BATheta_swap
#check @RBM.BA.BATheta_isSymm
#check @RBM.BA.BAMB_symm
#check @RBM.Loop.KLFlong
#check @RBM.Loop.KLTSPlong
#check @RBM.Loop.KLsigAlt
#check @RBM.Loop.diagonals
#check @RBM.Loop.sigmaIn
#check @RBM.Loop.sigmaOut
#check @RBM.Loop.Flong_eq_iff_cut
#check @RBM.Loop.exists_innermost
#check @RBM.Loop.Flong_subset_diagonals
#check @RBM.Loop.KLsum_cut
#check @RBM.Loop.KLgval
#check @RBM.Loop.KLKpi_eq_sum_SigmaPi
#check @RBM.Loop.SigSumZeroAbs
#check @RBM.Loop.IndStepAbs
