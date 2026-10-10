/-
Release check for T2396 (dispatcher V2, Sat Oct 10 22:11 UTC 2026; DECISIONS §209).  BA-K09b: the induction on molecules at BA,
`BAKpiBoundAt` for every `n ≥ 3` (new `BA/KStep.lean`; `Loop/KLInduct.lean` not edited).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2396-check.lean
-/
import RBM3D.BA.KInduct
import RBM3D.BA.KSumZeroB
import RBM3D.BA.KWardIneq
import RBM3D.BA.KPure
import RBM3D.Loop.KLInduct
import RBM3D.Loop.KLIndStepB

#check @RBM.BA.BAKpiBoundAt
#check @RBM.BA.BAKBoundAt
#check @RBM.BA.baKpi_cut_abs
#check @RBM.BA.baKpi_empty_slice
#check @RBM.BA.baKpi_empty_short
#check @RBM.BA.baSig_sumZeroAbs
#check @RBM.BA.baSig_decay
#check @RBM.BA.baWardIneq_holds
#check @RBM.Loop.IndStepAbs
#check @RBM.Loop.indStepAbs_of
#check @RBM.Loop.KLKpi_step
#check @RBM.Loop.KLInduct_KpiBoundAt_holds
#check @RBM.Loop.KLInduct_Kpi_empty_bound
#check @RBM.Loop.KLKpiBoundAt
