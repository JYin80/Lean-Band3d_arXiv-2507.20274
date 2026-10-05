/-
Release check for T2105 (dispatcher V1, Sun Oct  4 02:57 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-22: ports RBM2D `Green/FlucIterHigh`, `Green/MinorGoodLe` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2105-check.lean`.
-/
import RBM3D

#check @RBM.Green.integral_norm_flucAvg_pow_le_iter_budget
#check @RBM.Green.applyOps
#check @RBM.Green.BoundedWeight
#check @RBM.Green.condRow
