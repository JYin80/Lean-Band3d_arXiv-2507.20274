/-
Release check for T2016 (dispatcher V1, Sat Oct  3 01:49 UTC 2026; CLAUDE.md §4 step 0).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
EK-D1 is report-only (design of the evolution-kernel layer); this file checks that the merged
declarations it inventories and builds on exist on `main` (`RBM3D/Kernel/*`, PT-A = T2007 merged b20c658).
Run from the main worktree: `lake env lean docs/tickets/checks/T2016-check.lean`.
-/
import RBM3D

#check @RBM.cycProd
#check @RBM.thetaKer
#check @RBM.uKer
#check @RBM.ThetaN
#check @RBM.UN
#check @RBM.norm_UN_le
#check @RBM.avgOp
#check @RBM.zeroModeOp
#check @RBM.zeroModeSet
#check @RBM.SameSignOutside
#check @RBM.norm_zeroModeSet_UN_le
#check @RBM.propT
#check @RBM.sum_prod_norm_XiKer_le
#check @RBM.ThetaDecay
#check @RBM.ThetaDecayShort
#check @RBM.ThetaZeroMode
#check @RBM.Prop5Decay
#check @RBM.Prop5Short
#check @RBM.Prop8ZeroMode
#check @RBM.Prop5to8
#check @RBM.Bparam
#check @RBM.ellT
