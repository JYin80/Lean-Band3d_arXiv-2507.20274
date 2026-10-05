/-
Release check for T2135 (dispatcher V1, Sun Oct  4 12:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-07b: decay through cuts and label decay of the ℰ-terms; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2135-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STDecayLoopPT
#check @RBM.Gauss.Sizes.STDecayLoopAt
#check @RBM.Gauss.Sizes.STdiamInf
#check @RBM.Gauss.Sizes.stDecayLoopPT_of_step2
#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.EKFastDecay
#check @RBM.Gauss.Sizes.STegt
#check @RBM.Gauss.Sizes.STksimLK
#check @RBM.Gauss.Sizes.STelklk
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Gauss.Sizes.STSEforLnConcl
