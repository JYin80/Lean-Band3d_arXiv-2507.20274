/-
Release check for T2160 (dispatcher V1, Sun Oct  4 20:06 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-35: the `Y` moments: `YMomentsN`, `YMomentsUnifN`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2160-check.lean`.
-/
import RBM3D

#check @RBM.Ind.YMomentsN
#check @RBM.Ind.AssembledN
#check @RBM.Path.pathH
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
