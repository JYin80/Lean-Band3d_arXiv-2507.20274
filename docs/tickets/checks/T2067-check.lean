/-
Release check for T2067 (dispatcher V1, Sat Oct  3 18:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §24, §28).
LW-P moves the LW pins of the T2040 probe into the library, bound to the merged LW vocabulary; this file checks that
the merged names it binds to exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2067-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LData
#check @RBM.Graph.owxDefect
#check @RBM.Graph.lwG
#check @RBM.Graph.lwS
#check @RBM.Graph.lwSplus
#check @RBM.Graph.lwPoly
#check @RBM.Graph.dhSample
#check @RBM.Graph.Tame1
#check @RBM.Gauss.Sizes.Prec
#check @RBM.ellT
