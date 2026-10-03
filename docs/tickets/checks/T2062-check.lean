/-
Release check for T2062 (dispatcher V1, Sat Oct  3 18:44 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-34 ports RBM2D files at `c9a24cf` onto the merged MD layer and the merged ST-1 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2062-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STNetLift
#check @RBM.Ind.GopboundPin
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.Prec
