/-
Release check for T2096 (dispatcher V1, Sun Oct  4 00:42 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-21: ports Part 2 of RBM2D `Green/FlucIter` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2096-check.lean`.
-/
import RBM3D

#check @RBM.Green.applyOps
#check @RBM.Green.qRow
#check @RBM.Green.pivotWords
#check @RBM.Green.BoundedWeight
#check @RBM.Green.boundedWeight_svarF
#check @RBM.Green.LDE_norm_flucAvg_le_of_boundedWeight
