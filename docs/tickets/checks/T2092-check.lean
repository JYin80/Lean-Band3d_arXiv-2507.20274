/-
Release check for T2092 (dispatcher V1, Sun Oct  4 00:36 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-04: moves probe §10–§12.2 (iteration and closure of Step 2); this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2092-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STScaleExists
#check @RBM.Gauss.Sizes.stScaleExists_holds
#check @RBM.Gauss.Sizes.STNetLift2
#check @RBM.Gauss.Sizes.STLWT
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.STGoodAt
#check @RBM.Gauss.Sizes.STBctl_pos
