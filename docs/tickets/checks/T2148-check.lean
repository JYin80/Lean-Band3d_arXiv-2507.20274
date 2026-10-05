/-
Release check for T2148 (dispatcher V1, Sun Oct  4 17:32 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-28: `(zYU1)`, the pin `STWardII`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2148-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STWardII
#check @RBM.Gauss.Sizes.STWardIIConcl
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.zeroModeSet
#check @RBM.Loop.KLK_ward
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.ST_step5_caseII_of_pins
