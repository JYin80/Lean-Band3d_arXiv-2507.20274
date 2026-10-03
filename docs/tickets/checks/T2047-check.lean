/-
Release check for T2047 (dispatcher V1, Sat Oct  3 08:15 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The ticket ports RBM2D files at `c9a24cf` onto the merged MD layer and the merged ST-1 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2047-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.etaT
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STForbidden
#check @RBM.Gauss.Sizes.STBootstrap
#check @RBM.Gauss.Sizes.STNetLift
-- S1-01 (merged)
#check @RBM.Gauss.HflowBlock
#check @RBM.Gauss.norm_gloop_HflowBlock_le_crude_on_Icc
