/-
Release check for T2075 (dispatcher V1, Sat Oct  3 19:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §28).
ST2-06b: this file checks that the merged names the ticket builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2075-check.lean`.
-/
import RBM3D

#check @RBM.EKPropT
#check @RBM.ekPropT_holds
#check @RBM.Gauss.zdistInf
#check @RBM.zdistD
#check @RBM.tailT
