/-
Release check for T2173 (dispatcher V1, Mon Oct  5 03:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
BA-D2: the block Anderson form of Claim (417) (design supplement): the merged BA and size vocabulary it builds on;
this file checks that the merged names it builds on exist.  The UN and BA pins it extends are on the branches
`t/T2162` and `t/T2161` (probes, not merged).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2173-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiV
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.mE
