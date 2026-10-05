/-
Release check for T2098 (dispatcher V1, Sun Oct  4 00:42 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-26: ports RBM2D `Path/Expansion` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2098-check.lean`.
-/
import RBM3D

#check @RBM.Path.ukerMat
#check @RBM.Path.Uop
#check @RBM.Path.EE
#check @RBM.Path.QVPropagated
#check @RBM.Path.condExp_loop_drift
#check @RBM.Path.LoopGenN2
#check @RBM.Path.stepDecomp_loopPM
