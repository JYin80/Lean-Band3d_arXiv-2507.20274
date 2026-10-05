/-
Release check for T2132 (dispatcher V1, Sun Oct  4 11:34 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-13a: the `𝒬`-hierarchy on the grid: `gridDriftQN`, `stoppedDuhamelQN`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2132-check.lean`.
-/
import RBM3D

#check @RBM.Ind.Ugen
#check @RBM.Ind.AvecN
#check @RBM.Ind.martIncN
#check @RBM.Ind.predIncN
#check @RBM.Ind.StoppedDuhamelN
#check @RBM.Ind.stoppedDuhamelN
#check @RBM.Ind.GridDuhamelN_Ugen_duhamel_telescope
#check @RBM.Ind.stepErrN
#check @RBM.Ind.kStepC
#check @RBM.Ind.uStepC
#check @RBM.Ind.GridDriftN
#check @RBM.Ind.gridDriftN
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STAlternating
#check @RBM.Gauss.Sizes.STLKtensor
