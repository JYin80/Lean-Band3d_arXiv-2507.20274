/-
Release check for T2381 (dispatcher V2, Sat Oct 10 10:25 UTC 2026; DECISIONS §192).  BA-K10: `BA/KInduct.lean`, the base levels, the layer
form and `baKpi_cut` (the cut of `K^{(π)}` at an innermost long edge) for the molecule induction.  No new pin: the 1a fixes
the statements (design gate).  Merged names only.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2381-check.lean
-/
import RBM3D.BA.KMolecule
import RBM3D.BA.KCactusCut
import RBM3D.BA.KTreeRep
import RBM3D.BA.KSolve
import RBM3D.Loop.KLInduct
import RBM3D.Loop.KLIndStepB

#check @RBM.BA.BAKpi
#check @RBM.BA.baK_eq_sum_Kpi
#check @RBM.BA.baKpi_eq_sum_SigmaPi
#check @RBM.BA.baSigmaPi_cut
#check @RBM.BA.baCactus_cut
#check @RBM.BA.BAKsolveLe3
#check @RBM.BA.baK_unique
#check @RBM.BA.baKsolve
#check @RBM.BA.baTreeRep
#check @RBM.Loop.KLKpi_cut
#check @RBM.Loop.IndStepAbs
