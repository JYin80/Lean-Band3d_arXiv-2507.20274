/-
Release check for T2061 (dispatcher V1, Sat Oct  3 18:44 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-17 ports RBM2D files at `c9a24cf` onto the merged MD layer and the merged ST-1 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2061-check.lean`.
-/
import RBM3D

#check @RBM.green
#check @RBM.Green.minorGreen
#check @RBM.Green.minorMat
#check @RBM.Green.blkCoef2
#check @RBM.Green.sum_blkCoef2
#check @RBM.Green.goodSet
#check @RBM.Green.avg_bound_stochDom
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqP
