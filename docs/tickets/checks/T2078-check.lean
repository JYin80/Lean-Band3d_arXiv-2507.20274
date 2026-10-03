/-
Release check for T2078 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S1-18: ports RBM2D `Green/FlucAvg`, `Green/LDE` at `c9a24cf` with bounded weights (DECISIONS §30); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2078-check.lean`.
-/
import RBM3D

#check @RBM.Green.BoundedWeight
#check @RBM.Green.boundedWeight_svarF
#check @RBM.Green.flucVanish_blockAvg2_eq_blkCoef2
#check @RBM.Green.continuous_green_comp
#check @RBM.Green.avg_bound_stochDom
#check @RBM.Green.highProb_norm_rowSum_sq_le
