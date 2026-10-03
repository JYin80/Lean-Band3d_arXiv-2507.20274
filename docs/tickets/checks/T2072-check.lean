/-
Release check for T2072 (dispatcher V1, Sat Oct  3 19:38 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §28).
ST2-20: this file checks that the merged names the ticket builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2072-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.svarF
#check @RBM.Gauss.Xmat
