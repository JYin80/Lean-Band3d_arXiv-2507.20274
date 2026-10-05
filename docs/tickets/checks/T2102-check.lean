/-
Release check for T2102 (dispatcher V1, Sun Oct  4 01:27 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-09: proves the pin `STEMn2Poly`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2102-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STEMn2Poly
#check @RBM.Gauss.Sizes.STEEk
#check @RBM.Gauss.Sizes.STLWassm
#check @RBM.Gauss.Sizes.STInitialGT2
#check @RBM.Gauss.Sizes.STPsiClass
#check @RBM.Gauss.Sizes.STGbEXPij
#check @RBM.Gauss.Sizes.STGbEXPii
#check @RBM.Gauss.Sizes.stContractPt_holds
#check @RBM.Path.EE
