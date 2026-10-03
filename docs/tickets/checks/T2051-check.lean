/-
Release check for T2051 (dispatcher V1, Sat Oct  3 10:32 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §24).
LW-15 proves deterministic facts on the merged scale functions; this file checks that those names exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2051-check.lean`.
-/
import RBM3D

#check @RBM.tailT
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Prec
