/-
Release check for T2138 (dispatcher V1, Sun Oct  4 16:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-01: Step 5 pins into the library; checks the merged names the probe builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2138-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.tailT
#check @RBM.tailW
#check @RBM.BparamR
#check @RBM.Gauss.etaT
