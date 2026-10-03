/-
Release check for T2052 (dispatcher V1, Sat Oct  3 10:44 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
`#check` only: no proofs, no `sorry`.  Never imported or merged.
S1-14 ports RBM2D `Green/LDEQuadT` onto the merged S1-12 / S1-13 files; this file checks that the names it builds on exist.
Run from the main worktree: `lake env lean docs/tickets/checks/T2052-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.seqP
#check @RBM.Green.LDEQuad
#check @RBM.Green.Tame
#check @RBM.Green.RowChaos
#check @RBM.Green.RowChaos.mom_succ_le
#check @RBM.Green.RowChaos.Vq_eq_ldeQuadRHS
