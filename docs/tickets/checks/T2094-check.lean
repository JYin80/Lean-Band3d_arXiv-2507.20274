/-
Release check for T2094 (dispatcher V1, Sun Oct  4 00:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-08: proves the pin `STContractPt`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2094-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STContractPt
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.Sizes.stContract_holds
#check @RBM.sum_gloop_ward_last_div
#check @RBM.Gauss.zdistInf
