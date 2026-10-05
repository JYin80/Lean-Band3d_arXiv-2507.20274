/-
Release check for T2120 (dispatcher V1, Sun Oct  4 06:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-07: proves the owed pin `LWggExp` (`(Oe2x)`, fixed by DECISIONS §34) on `PF`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2120-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LWggExp
#check @RBM.Graph.LWPins_lwSp
#check @RBM.Graph.lwWeightExp_holds
#check @RBM.Graph.lwWxSizes
#check @RBM.Graph.lwWx_integral
#check @RBM.Graph.lwWx_lwPoly
#check @RBM.Graph.lwWx_lwdf
#check @RBM.Graph.lwWx_hSp
#check @RBM.Graph.lwWx_lwSp
#check @RBM.Graph.owx_integral
#check @RBM.Graph.stein_lwPoly
#check @RBM.Graph.owx_second
#check @RBM.Green.gaussIBP
