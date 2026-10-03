/-
Release check for T2079 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-35: ports the first part of RBM2D `Induction/Step1` at `c9a24cf` onto the merged ST-1 files; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2079-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STStep1
#check @RBM.Gauss.Sizes.stConArg_holds
#check @RBM.Gauss.Sizes.stNetLift_holds
#check @RBM.Ind.PerTimeCalc.Unif.forbidden_region
#check @RBM.StochDomAt
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.of_subset_union
#check @RBM.Gauss.Sizes.STFlow
