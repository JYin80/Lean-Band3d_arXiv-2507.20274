/-
Release check for T2130 (dispatcher V1, Sun Oct  4 11:03 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
ST2-16+17: `STLocalAvgOfL2` from `lem_GbEXP`, `(eq:L2_decay)` and `(Gtmwc)`; this file checks that the merged names it builds on exist.
`#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2130-check.lean`.
-/
import RBM3D

#check @RBM.Gauss.Sizes.STLocalAvgOfL2
#check @RBM.Gauss.Sizes.STStep2LocalPT
#check @RBM.Gauss.Sizes.STStep2AvgPT
#check @RBM.Gauss.Sizes.STL2decayPT
#check @RBM.Gauss.Sizes.STStep1Weak
#check @RBM.Gauss.Sizes.STInitialGT2
#check @RBM.Gauss.Sizes.STGbEXP
#check @RBM.Gauss.Sizes.STGiiGEX
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.Gauss.Sizes.STGavLGEX
#check @RBM.Gauss.Sizes.STgexRHS
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STindMax
#check @RBM.Green.stGbEXP_holds
#check @RBM.Green.perTime_timeIcc_of_forall_seq
#check @RBM.Gauss.Sizes.ST_step2_of_pins
#check @RBM.Gauss.Sizes.STFlow
