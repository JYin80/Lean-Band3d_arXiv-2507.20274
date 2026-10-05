/-
Release check for T2119 (dispatcher V1, Sun Oct  4 06:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-06: proves the owed pin `LWedgeExp` (`(Oe1x)`) on `PF` via T2107s bridge; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2119-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LWedgeExp
#check @RBM.Graph.LWPins_oe1xRest
#check @RBM.Graph.lwWeightExp_holds
#check @RBM.Graph.lwWxSizes
#check @RBM.Graph.lwWx_integral
#check @RBM.Graph.lwWx_lwPoly
#check @RBM.Graph.lwWx_lwdf
#check @RBM.Graph.stein_sample
#check @RBM.Graph.stein_lwPoly
#check @RBM.Graph.lwStein_dh_mul
#check @RBM.Graph.dhSample_lwG
#check @RBM.Graph.owxT1_counters
#check @RBM.Green.gaussIBP
