/-
Release check for T2175 (dispatcher V1, Mon Oct  5 05:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
UN-08 (GUEInvariance): the merged UN vocabulary (`RBM3D/Universality/Pins.lean`, T2174) and the other merged names the port builds on;
this file checks that they exist on `main`.  `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2175-check.lean`.
-/
import RBM3D

#check @RBM.Univ.gueP
#check @RBM.Univ.kPoint
#check @RBM.Univ.UNModel
#check @RBM.Univ.ouMat
#check @RBM.Gauss.SizesInst.sz0
