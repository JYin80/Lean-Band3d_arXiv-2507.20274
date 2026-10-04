/-
Release check for T2091 (dispatcher V1, Sun Oct  4 00:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-23: ports RBM2D `Green/IBP` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2091-check.lean`.
-/
import RBM3D

#check @RBM.Green.gaussIBP
#check @RBM.Green.GaussIBP
#check @RBM.Green.stochDom_ldeQuad
#check @RBM.Green.BoundedWeight
#check @RBM.Green.condRow
#check @RBM.Gauss.svarF
