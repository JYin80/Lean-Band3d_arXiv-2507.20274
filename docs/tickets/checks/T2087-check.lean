/-
Release check for T2087 (dispatcher V1, Sat Oct  3 22:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S3-24a: ports the first part of RBM2D `Induction/Step3` and the probe `≺`-helpers; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2087-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STPsi
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STIterations
#check @RBM.Gauss.Sizes.st_iterate
#check @RBM.Gauss.Sizes.st_Bctl_ge
#check @RBM.Ind.loopXi_le
#check @RBM.Gauss.Sizes.Prec
