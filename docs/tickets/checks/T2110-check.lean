/-
Release check for T2110 (dispatcher V1, Sun Oct  4 03:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-14: `(eq:opt_L2)` part 1 (pin `STOptL2`, conditional on `STLWB`, `STGridMart`); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2110-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STOptL2
#check @RBM.Gauss.Sizes.STLWB
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.Gauss.Sizes.stNewKLK_holds
#check @RBM.Gauss.Sizes.stEMn2Poly_holds
#check @RBM.Gauss.Sizes.ST_gronwall
#check @RBM.Gauss.Sizes.ST_grid_whp_of_sections
#check @RBM.Gauss.Sizes.ST_step2_of_pins'
