/-
Release check for T2121 (dispatcher V1, Sun Oct  4 06:51 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-30: ports RBM2D `Induction/StepDecompN` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2121-check.lean`.
-/
import RBM3D

#check @RBM.Ind.hermTestFunLoopN
#check @RBM.Ind.HermTestFunLoopN
#check @RBM.Ind.gridDriftN
#check @RBM.Ind.loopDerivN
#check @RBM.Ind.martIncN
#check @RBM.Ind.Ugen
#check @RBM.Path.stepDecomp
#check @RBM.Path.stepDecomp_Z_subG
#check @RBM.Path.condExp_loop_step
