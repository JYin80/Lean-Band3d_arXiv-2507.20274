/-
Release check for T2083 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-21: ports RBM2D `Path/LoopStep`, `Path/DriftAlgebra` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2083-check.lean`.
-/
import RBM3D

#check @RBM.Path.genMat
#check @RBM.Path.envConst
#check @RBM.Path.OneStepEnvelope
#check @RBM.Gauss.Sizes.Lloop
