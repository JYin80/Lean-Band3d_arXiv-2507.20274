/-
Release check for T2097 (dispatcher V1, Sun Oct  4 00:42 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-25: ports RBM2D `Path/UBounds`, `Path/UTransport`, `Path/KellStar` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2097-check.lean`.
-/
import RBM3D

#check @RBM.Path.ukerMat
#check @RBM.Path.Uop
#check @RBM.Path.stepDecomp_loopPM
#check @RBM.EKSumNdecay
#check @RBM.ekSumNdecay_holds
#check @RBM.Gauss.Sizes.STK2decay
