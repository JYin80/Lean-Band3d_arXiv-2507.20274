/-
Release check for T2085 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-24: ports RBM2D `Path/StepDecompLoop`, `Path/Kernel` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2085-check.lean`.
-/
import RBM3D

#check @RBM.Path.gradMat
#check @RBM.Path.HermTestFun
#check @RBM.Path.stepDecomp
#check @RBM.Gauss.Sizes.Lloop
