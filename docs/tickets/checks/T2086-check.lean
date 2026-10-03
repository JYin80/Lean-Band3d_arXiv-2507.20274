/-
Release check for T2086 (dispatcher V1, Sat Oct  3 22:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-03: proves the pin `STNewPQ`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2086-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STNewPQ
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.zeroModeSet
#check @RBM.zeroModeOp
#check @RBM.avgOp
#check @RBM.Loop.KLK_ward
#check @RBM.sum_gloop_ward_last_div
