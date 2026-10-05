/-
Release check for T2147 (dispatcher V1, Sun Oct  4 17:32 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-04: `TailtoTail` `(neiwuj)`, the pin `STTailtoTail`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2147-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.tailTD
#check @RBM.UN
#check @RBM.EKsgn
#check @RBM.Theta
#check @RBM.Gauss.zdistInf
