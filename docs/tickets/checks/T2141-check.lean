/-
Release check for T2141 (dispatcher V1, Sun Oct  4 16:16 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
S5-19: far-entry decay of the resolvent (port of RBM2D FarEntry); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2141-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STGbEXPij
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.Gauss.Sizes.STgexRHS
#check @RBM.Gauss.Sizes.STindMax
#check @RBM.Green.stGbEXPij_of_v3
#check @RBM.Green.gbEXPV3
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.STblk
#check @RBM.ellT
#check @RBM.Gauss.Sizes.stKcalDecay_holds
#check @RBM.Path.kellStarEv
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Sizes.STLK_of_STLKU
