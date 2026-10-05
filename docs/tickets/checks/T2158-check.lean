/-
Release check for T2158 (dispatcher V1, Sun Oct  4 19:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-14: the kernel facts of the Step 5 Duhamel step; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2158-check.lean`.
-/
import RBM3D

#check @RBM.UN
#check @RBM.EKsgn
#check @RBM.Theta
#check @RBM.norm_Theta_le
#check @RBM.ekPropTInf_holds
#check @RBM.tailT
#check @RBM.tailW
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.stTailtoTail_holds
