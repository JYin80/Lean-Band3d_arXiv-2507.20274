/-
Release check for T2103 (dispatcher V1, Sun Oct  4 02:13 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-28: ports RBM2D `Induction/LoopGenN`, `Induction/QVN` and proves `STLoopGenNForm`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2103-check.lean`.
-/
import RBM3D

#check @RBM.Ind.STLoopGenNForm
#check @RBM.Ind.HierarchyN
#check @RBM.Ind.hierarchyN_of_loopGenN
#check @RBM.Path.LoopGenN2
#check @RBM.Path.QVPropagated
#check @RBM.Path.EE
