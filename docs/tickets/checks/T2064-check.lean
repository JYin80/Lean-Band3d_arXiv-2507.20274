/-
Release check for T2064 (dispatcher V1, Sat Oct  3 18:44 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-05 ports RBM2D files at `c9a24cf` onto the merged MD layer and the merged ST-1 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2064-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.coordinateBlock
#check @RBM.Gauss.HflowBlock_update
#check @RBM.Gauss.gsigCoordinateDeriv
#check @RBM.Gauss.gloop
#check @RBM.Gauss.CoordF
