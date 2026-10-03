/-
Release check for T2050 (dispatcher V1, Sat Oct  3 10:32 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §24).
LW-03 builds the graph vocabulary on the merged `RBM3D/Graph` files and the model; this file checks that those names exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2050-check.lean`.
-/
import RBM3D

#check @RBM.Graph.Counters
#check @RBM.Graph.ord
#check @RBM.Graph.Case
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Gres
