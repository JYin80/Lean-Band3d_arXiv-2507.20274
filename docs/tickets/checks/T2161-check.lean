/-
Release check for T2161 (dispatcher V1, Sun Oct  4 20:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
BA-D1: block Anderson design: the merged BA vocabulary it builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2161-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Gauss.Sizes.Gt_BA
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Theta
