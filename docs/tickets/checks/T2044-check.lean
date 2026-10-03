/-
Release check for T2044 (dispatcher V1, Sat Oct  3 07:57 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-13 ports RBM2D `Green/LDEQuadMom` onto the merged S1-10 / S1-12 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2044-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Green.LDEQuad
#check @RBM.Green.GoodEvent
#check @RBM.Green.FinDep
#check @RBM.Green.polyW
#check @RBM.Green.Tame
#check @RBM.Green.GaussIBP
