/-
Release check for T2107 (dispatcher V1, Sun Oct  4 03:19 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
LW-05: proves the owed pin `LWweightExp` (`(Owx)`) on `PF` via the merged Stein layer; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2107-check.lean`.
-/
import RBM3D

#check @RBM.Graph.LWweightExp
#check @RBM.Graph.LWPins_lwG
#check @RBM.Graph.LWPins_dH
#check @RBM.Graph.LWPins_lwSp
#check @RBM.Graph.LWPins_resPoly
#check @RBM.Graph.owx_integral
#check @RBM.Graph.owx_defect_identity
#check @RBM.Graph.lwPoly
#check @RBM.Graph.lwG
#check @RBM.Graph.lwS
#check @RBM.Graph.dhSample
#check @RBM.Graph.dhSample_lwG_eq_deriv
#check @RBM.Graph.owx_second
#check @RBM.Graph.owx_smallest_E
#check @RBM.Graph.owx_ord
#check @RBM.Graph.owx_ord_H
#check @RBM.Green.gaussIBP
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.PF
