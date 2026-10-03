/-
Release check for T2073 (dispatcher V1, Sat Oct  3 19:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §28).
ST2-22: this file checks that the merged names the ticket builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2073-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqGvar
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Xmat
