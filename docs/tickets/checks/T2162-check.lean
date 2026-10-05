/-
Release check for T2162 (dispatcher V1, Sun Oct  4 20:53 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
UN-D1: bulk universality design: the merged vocabulary it builds on; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2162-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.Hmat
#check @RBM.Gauss.Xmat
#check @RBM.mE
#check @RBM.Gauss.Gres
#check @RBM.Theta
