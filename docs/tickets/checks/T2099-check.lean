/-
Release check for T2099 (dispatcher V1, Sun Oct  4 00:56 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-07: proves the pin `STNewKLK`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2099-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.Gauss.Sizes.STNewKLKAt
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STJhatM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STGMM
#check @RBM.Gauss.Sizes.stK2decay_holds
#check @RBM.ekPropTInf_holds
#check @RBM.Loop.KLK_ward
