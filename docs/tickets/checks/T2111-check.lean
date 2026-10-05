/-
Release check for T2111 (dispatcher V1, Sun Oct  4 03:48 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-29: ports RBM2D `Induction/LoopC2N`, `Induction/GridDriftN` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2111-check.lean`.
-/
import RBM3D

#check @RBM.Path.HermTestFun
#check @RBM.Path.hermTestFun_loopPM
#check @RBM.Path.stepDecomp
#check @RBM.Path.condExp_loop_drift
#check @RBM.Ind.loopGenN
#check @RBM.Ind.hierarchyN_holds
#check @RBM.Ind.Ugen
#check @RBM.ThetaN
#check @RBM.UN
#check @RBM.Gauss.norm_gloop_le_crude
