/-
Release check for T2112 (dispatcher V1, Sun Oct  4 03:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-20: the zero-mode calculus `Q^(A)` of Step 3 case (ii); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2112-check.lean`.
-/
import RBM3D

#check @RBM.avgOp
#check @RBM.zeroModeSet
#check @RBM.projMat
#check @RBM.zeroModeSet_tensorKer
#check @RBM.projMat_mul_SB_comm
#check @RBM.projMat_mul_Theta
#check @RBM.norm_projMat_le
#check @RBM.norm_zeroModeSet_UN_le
#check @RBM.ThetaN
#check @RBM.thetaKer
#check @RBM.tensorKer
#check @RBM.UN_eq_tensorKer
#check @RBM.Ind.GridDuhamelN_Ugen_duhamel_telescope
#check @RBM.Ind.stoppedDuhamelN
#check @RBM.Gauss.Sizes.STOeqQtNZ
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.stNewPQ_holds
