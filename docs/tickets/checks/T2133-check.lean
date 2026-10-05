/-
Release check for T2133 (dispatcher V1, Sun Oct  4 11:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-07a: `lem_decayLoop`: `STDecayLoopAt`, `STDecayLoopPT`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2133-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.stKcalDecay_holds
#check @RBM.Gauss.Sizes.STStep2DecayPT
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.zdistInf
#check @RBM.Loop.KLmaxDist
#check @RBM.Ind.norm_sq_gloop_le_symIdx
#check @RBM.Ind.norm_gloop_le_of_le_abs_im
#check @RBM.Green.perTime_timeIcc_of_forall_seq
