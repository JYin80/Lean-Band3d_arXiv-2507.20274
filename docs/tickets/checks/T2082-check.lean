/-
Release check for T2082 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-19: ports the rest of RBM2D `Path/NetLift` and closes `STNetLift2`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2082-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STNetLift2
#check @RBM.Gauss.Sizes.stNetLift2_part1
#check @RBM.Ind.Step2NetLift
#check @RBM.Ind.step2NetLift
#check @RBM.Gauss.Sizes.stNetLift_holds
