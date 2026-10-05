/-
Release check for T2101 (dispatcher V1, Sun Oct  4 01:27 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-24: ports RBM2D `Green/CondDom`, `Green/CondStable`, `Green/EntryGauss` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2101-check.lean`.
-/
import RBM3D

#check @RBM.Green.ibpRem_eq_add
#check @RBM.Green.condExpDiag_eq_sum_Sblk
#check @RBM.Green.gaussIBP
#check @RBM.Green.avg_bound_stochDom
#check @RBM.StochDomAt
#check @RBM.Green.BoundedWeight
