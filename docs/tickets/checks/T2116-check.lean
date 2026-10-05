/-
Release check for T2116 (dispatcher V1, Sun Oct  4 06:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-15: `(eq:opt_L2)` part 2 (pin `STOptL2`, conditional on `STLWB`, `STGridMart`); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2116-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STOptL2
#check @RBM.Gauss.Sizes.STLWB
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.stOptL2a_gronwall
#check @RBM.Gauss.Sizes.stOptL2a_drift
#check @RBM.Gauss.Sizes.stOptL2a_martingale
#check @RBM.Gauss.Sizes.ST_gronwall
#check @RBM.Gauss.Sizes.ST_logsum
#check @RBM.Gauss.Sizes.ST_PT_of_sections
#check @RBM.Gauss.Sizes.ST_model_le_path
