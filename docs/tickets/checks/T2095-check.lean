/-
Release check for T2095 (dispatcher V1, Sun Oct  4 00:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-28a: ports RBM2D `Induction/HierAlgebra`, `Induction/HierarchyN`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2095-check.lean`.
-/
import RBM3D

#check @RBM.Path.HierarchyN2
#check @RBM.Path.LoopGenN2
#check @RBM.Path.hierarchyN2
#check @RBM.Gauss.Sizes.STLI
#check @RBM.Gauss.Sizes.STee
