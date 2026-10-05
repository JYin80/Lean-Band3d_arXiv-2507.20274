/-
Release check for T2164 (dispatcher V1, Sun Oct  4 21:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-05: lem_dec_calE first part: the merged Step 5 vocabulary and Green-function pins it builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2164-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.tailTD
#check @RBM.Gauss.Sizes.STIngR5
