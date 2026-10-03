/-
Release check for T2084 (dispatcher V1, Sat Oct  3 21:59 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-23: ports RBM2D `Path/QVForm`, `Path/QVIdentity` at `c9a24cf`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2084-check.lean`.
-/
import RBM3D

#check @RBM.Path.gradMat
#check @RBM.Path.HermTestFun
#check @RBM.Path.stepDecomp
