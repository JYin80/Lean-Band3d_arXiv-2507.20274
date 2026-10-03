/-
Release check for T2033 (dispatcher V1, Sat Oct  3 05:13 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-09 ports RBM2D files at `c9a24cf` onto the merged MD layer; this file checks that the merged vocabulary it builds on exists.
Run from the main worktree: `lake env lean docs/tickets/checks/T2033-check.lean`.
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
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.ellT
#check @RBM.mE
