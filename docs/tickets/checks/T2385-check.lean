/-
Release check for T2385 (dispatcher V2, Sat Oct 10 12:16 UTC 2026; DECISIONS §197).  BA-K08a: `BA/KSumZeroA.lean`, the signed sum-zero of
`BASig` and the Ward bound for sums of `𝒦`; its 1a is the design gate for K08a and K08b (supervisor 2051 Q4, K-b).
No new pin.  Merged names only.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2385-check.lean
-/
import RBM3D.BA.KPure
import RBM3D.BA.KWard
import RBM3D.BA.KInduct
import RBM3D.BA.KMolecule
import RBM3D.Loop.KLIndStepA
import RBM3D.Loop.KLSumZero

#check @RBM.BA.BASig
#check @RBM.BA.baSig_decay
#check @RBM.BA.baSig_transl
#check @RBM.BA.baK_ward
#check @RBM.BA.baKpi_empty_slice
#check @RBM.BA.BATheta_row_sum_pm
#check @RBM.Loop.SigSumZeroAbs
#check @RBM.Loop.KLsigAlt
#check @RBM.Loop.SumZero_sum_Kpi_eq
