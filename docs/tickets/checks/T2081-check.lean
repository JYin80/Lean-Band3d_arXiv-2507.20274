/-
Release check for T2081 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-05: proves the pin `STScaleExists`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2081-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STScaleExists
#check @RBM.Gauss.Sizes.STScaleAdm
#check @RBM.tailT
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STBctl_pos
