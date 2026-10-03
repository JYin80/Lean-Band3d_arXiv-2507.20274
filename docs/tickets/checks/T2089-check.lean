/-
Release check for T2089 (dispatcher V1, Sat Oct  3 22:39 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-20: ports the first part of RBM2D `Green/FlucIter` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2089-check.lean`.
-/
import RBM3D

#check @RBM.Green.condRow
#check @RBM.Green.FinDep
#check @RBM.Green.BoundedWeight
#check @RBM.Green.boundedWeight_svarF
#check @RBM.Green.LDE_norm_flucAvg_le_of_boundedWeight
