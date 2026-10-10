/-
Release check for T2384 (dispatcher V2, Sat Oct 10 12:00 UTC 2026; DECISIONS §195).  BA-K11: `BA/KWardIneq.lean`, `lem_wardineq_K` for the
BA `𝒦` (twin of `Loop/KLWardIneq.lean`).  No new pin: the 1a fixes the statements (design gate).  Merged names only.
No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2384-check.lean
-/
import RBM3D.BA.KInduct
import RBM3D.BA.KWard
import RBM3D.BA.KMolecule
import RBM3D.Loop.KLWardIneq

#check @RBM.BA.BAKBoundAt
#check @RBM.BA.BAKpiBoundAt
#check @RBM.BA.baKpi_cut
#check @RBM.BA.baKpi_empty_slice
#check @RBM.BA.baK_ward
#check @RBM.BA.BAKpi
#check @RBM.BA.baK_eq_sum_Kpi
#check @RBM.Loop.KLwardIneqAt
#check @RBM.Loop.KLWardIneq_Kpi_step
