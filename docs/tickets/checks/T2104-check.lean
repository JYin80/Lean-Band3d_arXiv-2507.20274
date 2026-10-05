/-
Release check for T2104 (dispatcher V1, Sun Oct  4 02:42 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-27: ports RBM2D `Path/DuhamelTail`, `Induction/GridDuhamelN` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2104-check.lean`.
-/
import RBM3D

#check @RBM.Path.StoppedDuhamel105
#check @RBM.Path.Avec
#check @RBM.Path.grid_expansion_all
#check @RBM.Path.Uop
#check @RBM.Path.ukerMat
