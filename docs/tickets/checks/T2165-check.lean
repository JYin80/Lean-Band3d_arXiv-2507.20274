/-
Release check for T2165 (dispatcher V1, Sun Oct  4 21:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-23: CLT moment counting part 1: the merged Step 5 CLT vocabulary, isolation bound, mean part and propagator facts it builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2165-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.stCltIso_holds
#check @RBM.Gauss.Sizes.meanFar_core
#check @RBM.prop5Decay_holds
#check @RBM.prop6Diff1_holds
#check @RBM.sum_radial
#check @RBM.card_sphere_le
