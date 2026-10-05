/-
Release check for T2136 (dispatcher V1, Sun Oct  4 12:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-19: `STWardTypePPin`, `STB45Pin`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2136-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STWardTypePPin
#check @RBM.Gauss.Sizes.STB45Pin
#check @RBM.Gauss.Sizes.STWardTypeP
#check @RBM.Gauss.Sizes.STB45
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN
#check @RBM.Gauss.Sizes.STDecayLoopPT
#check @RBM.Gauss.Sizes.stDecayLoopPT_of_step2
#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2DecayPT
