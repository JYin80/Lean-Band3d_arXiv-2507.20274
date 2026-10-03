/-
Release check for T2038 (dispatcher V1, Sat Oct  3 05:55 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
The ticket ports RBM2D files at `c9a24cf` onto the merged MD layer and the merged ST-1 files; this file checks that the vocabulary it builds on exists.
Run from the main worktree: `lake env lean docs/tickets/checks/T2038-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.svarF
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Gres
#check @RBM.Gauss.blockMat
#check @RBM.Loop.LoopIdx
-- S1-10 (merged)
#check @RBM.Green.GoodEvent
#check @RBM.Green.LDERow
#check @RBM.Green.norm_condExp_le
