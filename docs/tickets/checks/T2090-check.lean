/-
Release check for T2090 (dispatcher V1, Sun Oct  4 00:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-36: ports the second part of RBM2D `Induction/Step1` and proves `Step1TargetV3`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2090-check.lean`.
-/
import RBM3D

#check @RBM.Ind.Step1TargetV3
#check @RBM.Ind.stStep1_of_target
#check @RBM.Ind.S1Std
#check @RBM.Gauss.Sizes.STStep1
#check @RBM.Gauss.Sizes.STGbEXPii
#check @RBM.Gauss.Sizes.stConArg_holds
#check @RBM.Gauss.Sizes.stNetLift_holds
#check @RBM.Ind.PerTimeCalc.Unif.forbidden_region
