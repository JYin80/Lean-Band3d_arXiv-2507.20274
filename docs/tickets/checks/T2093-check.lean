/-
Release check for T2093 (dispatcher V1, Sun Oct  4 00:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-06: proves the pin `STK2decay`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2093-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STK2decay
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Loop.KLK_two
#check @RBM.Prop5Decay
