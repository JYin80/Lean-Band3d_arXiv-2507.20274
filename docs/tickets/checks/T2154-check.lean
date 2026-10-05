/-
Release check for T2154 (dispatcher V1, Sun Oct  4 18:35 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-33: assembly of the stopped grid evolution (pins + port of RBM2D GridAssemblyN); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2154-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.GridGoodN
#check @RBM.Path.pathH
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridTime
