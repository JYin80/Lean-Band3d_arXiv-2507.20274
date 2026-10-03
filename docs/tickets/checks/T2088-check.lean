/-
Release check for T2088 (dispatcher V1, Sat Oct  3 22:39 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-19: ports RBM2D `Green/IBPPoly`, `Green/LDEQuadInst` at `c9a24cf` and proves `GaussIBP`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2088-check.lean`.
-/
import RBM3D

#check @RBM.Green.GaussIBP
#check @RBM.Green.FinDep
#check @RBM.Green.polyW
#check @RBM.Green.RowChaos.momTpow_le
#check @RBM.Green.stochDom_normSq_Hflow_diag
#check @RBM.Green.highProb_norm_rowSum_sq_le
#check @RBM.Gauss.svarF
