/-
Release check for T2134 (dispatcher V1, Sun Oct  4 12:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST-D4: Step 5 design; checks the merged names the pins build on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2134-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.STEKSumNdecay
#check @RBM.Gauss.Sizes.STEKSumRes1
#check @RBM.tailT
#check @RBM.tailW
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.Gauss.etaT
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STKloop
