/-
Release check for T2118 (dispatcher V1, Sun Oct  4 06:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-11: third estimate of `lem: EMn2_N`, part 2 (pin `STEMn2Exp`); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2118-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Gauss.Sizes.emn2Exp_of_far3
#check @RBM.Gauss.Sizes.emn2ExpS3M
#check @RBM.Gauss.Sizes.emn2Exp_EEk_split
#check @RBM.Gauss.Sizes.emn2Exp_kellStar_far
#check @RBM.Gauss.Sizes.emn2Exp_near
#check @RBM.Gauss.Sizes.emn2Exp_far12
#check @RBM.Gauss.Sizes.stK2decay_holds
#check @RBM.Gauss.Sizes.STJhat
#check @RBM.Gauss.Sizes.STprof
#check @RBM.ekPropT_holds
#check @RBM.EKPropT
