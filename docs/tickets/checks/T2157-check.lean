/-
Release check for T2157 (dispatcher V1, Sun Oct  4 19:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-22b: the mean part of `f^{far}`, `(eq:boundEfar)`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2157-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STExpInv
#check @RBM.Gauss.Sizes.stExpInv_holds
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Theta
#check @RBM.Prop7Diff2
#check @RBM.prop7Diff2_holds
#check @RBM.Prop6Diff1
#check @RBM.prop6Diff1_holds
#check @RBM.Gauss.Sizes.STGdecayW
